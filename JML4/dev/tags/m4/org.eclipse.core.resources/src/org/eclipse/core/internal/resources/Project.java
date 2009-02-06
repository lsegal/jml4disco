/*******************************************************************************
 * Copyright (c) 2000, 2008 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.core.internal.resources;

import java.net.URI;
import java.util.*;
import org.eclipse.core.filesystem.*;
import org.eclipse.core.internal.events.LifecycleEvent;
import org.eclipse.core.internal.utils.*;
import org.eclipse.core.resources.*;
import org.eclipse.core.resources.team.IMoveDeleteHook;
import org.eclipse.core.runtime.*;
import org.eclipse.core.runtime.content.IContentTypeMatcher;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.osgi.util.NLS;

public class Project extends Container implements IProject {

	protected Project(IPath path, Workspace container) {
		super(path, container);
	}
	
	protected void assertCreateRequirements(IProjectDescription description) throws CoreException {
		checkDoesNotExist();
		checkDescription(this, description, false);
		URI location = description.getLocationURI();
		if (location != null)
			return;
		//if the project is in the default location, need to check for collision with existing folder of different case
		if (!Workspace.caseSensitive) {
			IFileStore store = getStore();
			IFileInfo localInfo = store.fetchInfo();
			if (localInfo.exists()) {
				String name = getLocalManager().getLocalName(store);
				if (name != null && !store.getName().equals(name)) {
					String msg = NLS.bind(Messages.resources_existsLocalDifferentCase, new Path(store.toString()).removeLastSegments(1).append(name).toOSString());
					throw new ResourceException(IResourceStatus.CASE_VARIANT_EXISTS, getFullPath(), msg, null);
				}
			}
		}
	}

	/*
	 * If the creation boolean is true then this method is being called on project creation.
	 * Otherwise it is being called via #setDescription. The difference is that we don't allow
	 * some description fields to change value after project creation. (e.g. project location)
	 */
	protected MultiStatus basicSetDescription(ProjectDescription description, int updateFlags) {
		String message = Messages.resources_projectDesc;
		MultiStatus result = new MultiStatus(ResourcesPlugin.PI_RESOURCES, IResourceStatus.FAILED_WRITE_METADATA, message, null);
		ProjectDescription current = internalGetDescription();
		current.setComment(description.getComment());
		// set the build order before setting the references or the natures
		current.setBuildSpec(description.getBuildSpec(true));

		// set the references before the natures 
		boolean flushOrder = false;
		IProject[] oldReferences = current.getReferencedProjects();
		IProject[] newReferences = description.getReferencedProjects();
		if (!Arrays.equals(oldReferences, newReferences)) {
			current.setReferencedProjects(newReferences);
			flushOrder = true;
		}
		oldReferences = current.getDynamicReferences();
		newReferences = description.getDynamicReferences();
		if (!Arrays.equals(oldReferences, newReferences)) {
			current.setDynamicReferences(newReferences);
			flushOrder = true;
		}

		if (flushOrder)
			workspace.flushBuildOrder();

		// the natures last as this may cause recursive calls to setDescription.
		if ((updateFlags & IResource.AVOID_NATURE_CONFIG) == 0)
			workspace.getNatureManager().configureNatures(this, current, description, result);
		else
			current.setNatureIds(description.getNatureIds(false));
		return result;
	}

	/* (non-Javadoc)
	 * @see IProject#build(int, IProgressMonitor)
	 */
	public void build(int trigger, IProgressMonitor monitor) throws CoreException {
		internalBuild(trigger, null, null, monitor);
	}

	/* (non-Javadoc)
	 * @see IProject#build(int, String, Map, IProgressMonitor)
	 */
	public void build(int trigger, String builderName, Map args, IProgressMonitor monitor) throws CoreException {
		Assert.isNotNull(builderName);
		internalBuild(trigger, builderName, args, monitor);
	}

	/**
	 * Checks that this resource is accessible.  Typically this means that it
	 * exists.  In the case of projects, they must also be open.
	 * If phantom is true, phantom resources are considered.
	 *
	 * @exception CoreException if this resource is not accessible
	 */
	public void checkAccessible(int flags) throws CoreException {
		super.checkAccessible(flags);
		if (!isOpen(flags)) {
			String message = NLS.bind(Messages.resources_mustBeOpen, getFullPath());
			throw new ResourceException(IResourceStatus.PROJECT_NOT_OPEN, getFullPath(), message, null);
		}
	}

	/**
	 * Checks validity of the given project description.
	 */
	protected void checkDescription(IProject project, IProjectDescription desc, boolean moving) throws CoreException {
		URI location = desc.getLocationURI();
		String message = Messages.resources_invalidProjDesc;
		MultiStatus status = new MultiStatus(ResourcesPlugin.PI_RESOURCES, IResourceStatus.INVALID_VALUE, message, null);
		status.merge(workspace.validateName(desc.getName(), IResource.PROJECT));
		if (moving) {
			// if we got here from a move call then we should check the location in the description since
			// its possible that we want to do a rename without moving the contents. (and we shouldn't
			// throw an Overlapping mapping exception in this case) So if the source description's location
			// is null (we are using the default) or if the locations aren't equal, then validate the location
			// of the new description. Otherwise both locations aren't null and they are equal so ignore validation.
			URI sourceLocation = internalGetDescription().getLocationURI();
			if (sourceLocation == null || !sourceLocation.equals(location))
				status.merge(workspace.validateProjectLocationURI(project, location));
		} else
			// otherwise continue on like before
			status.merge(workspace.validateProjectLocationURI(project, location));
		if (!status.isOK())
			throw new ResourceException(status);
	}

	/* (non-Javadoc)
	 * @see IProject#close(IProgressMonitor)
	 */
	public void close(IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		try {
			String msg = NLS.bind(Messages.resources_closing_1, getName());
			monitor.beginTask(msg, Policy.totalWork);
			final ISchedulingRule rule = workspace.getRuleFactory().modifyRule(this);
			try {
				workspace.prepareOperation(rule, monitor);
				ResourceInfo info = getResourceInfo(false, false);
				int flags = getFlags(info);
				checkExists(flags, true);
				monitor.subTask(msg);
				if (!isOpen(flags))
					return;
				// Signal that this resource is about to be closed.  Do this at the very 
				// beginning so that infrastructure pieces have a chance to do clean up 
				// while the resources still exist.
				workspace.beginOperation(true);
				workspace.broadcastEvent(LifecycleEvent.newEvent(LifecycleEvent.PRE_PROJECT_CLOSE, this));
				// flush the build order early in case there is a problem
				workspace.flushBuildOrder();
				IProgressMonitor sub = Policy.subMonitorFor(monitor, Policy.opWork / 2, SubProgressMonitor.SUPPRESS_SUBTASK_LABEL);
				IStatus saveStatus = workspace.getSaveManager().save(ISaveContext.PROJECT_SAVE, this, sub);
				internalClose();
				monitor.worked(Policy.opWork / 2);
				if (saveStatus != null && !saveStatus.isOK())
					throw new ResourceException(saveStatus);
			} catch (OperationCanceledException e) {
				workspace.getWorkManager().operationCanceled();
				throw e;
			} finally {
				workspace.endOperation(rule, true, Policy.subMonitorFor(monitor, Policy.endOpWork));
			}
		} finally {
			monitor.done();
		}
	}

	/* (non-Javadoc)
	 * @see IResource#copy(IPath, int, IProgressMonitor)
	 */
	public void copy(IPath destination, int updateFlags, IProgressMonitor monitor) throws CoreException {
		// FIXME - the logic here for copying projects needs to be moved to Resource.copy
		//   so that IResource.copy(IPath,int,IProgressMonitor) works properly for
		//   projects and honours all update flags
		monitor = Policy.monitorFor(monitor);
		if (destination.segmentCount() == 1) {
			// copy project to project
			String projectName = destination.segment(0);
			IProjectDescription desc = getDescription();
			desc.setName(projectName);
			desc.setLocation(null);
			internalCopy(desc, updateFlags, monitor);
		} else {
			// will fail since we're trying to copy a project to a non-project
			checkCopyRequirements(destination, IResource.PROJECT, updateFlags);
		}
	}

	/* (non-Javadoc)
	 * @see IResource#copy(IProjectDescription, int, IProgressMonitor)
	 */
	public void copy(IProjectDescription destination, int updateFlags, IProgressMonitor monitor) throws CoreException {
		// FIXME - the logic here for copying projects needs to be moved to Resource.copy
		//   so that IResource.copy(IProjectDescription,int,IProgressMonitor) works properly for
		//   projects and honours all update flags
		Assert.isNotNull(destination);
		internalCopy(destination, updateFlags, monitor);
	}

	protected void copyMetaArea(IProject source, IProject destination, IProgressMonitor monitor) throws CoreException {
		IFileStore oldMetaArea = EFS.getFileSystem(EFS.SCHEME_FILE).getStore(workspace.getMetaArea().locationFor(source));
		IFileStore newMetaArea = EFS.getFileSystem(EFS.SCHEME_FILE).getStore(workspace.getMetaArea().locationFor(destination));
		oldMetaArea.copy(newMetaArea, EFS.NONE, monitor);
	}

	/* (non-Javadoc)
	 * @see IProject#create(IProgressMonitor)
	 */
	public void create(IProgressMonitor monitor) throws CoreException {
		create(null, monitor);
	}
	
	/* (non-Javadoc)
	 * @see IProject#create(IProjectDescription, IProgressMonitor)
	 */
	public void create(IProjectDescription description, IProgressMonitor monitor) throws CoreException {
		create(description, IResource.NONE, monitor);
	}
	
	/* (non-Javadoc)
	 * @see IProject#create(IProjectDescription, IProgressMonitor)
	 */
	public  void create(IProjectDescription description, int updateFlags, IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		try {
			monitor.beginTask(Messages.resources_create, Policy.totalWork);
			checkValidPath(path, PROJECT, false);
			final ISchedulingRule rule = workspace.getRuleFactory().createRule(this);
			try {
				workspace.prepareOperation(rule, monitor);				
				if (description == null) {
					description = new ProjectDescription();
					description.setName(getName());
				}		
				assertCreateRequirements(description);
				workspace.broadcastEvent(LifecycleEvent.newEvent(LifecycleEvent.PRE_PROJECT_CREATE, this));
				workspace.beginOperation(true);
				workspace.createResource(this, updateFlags);
				workspace.getMetaArea().create(this);
				ProjectInfo info = (ProjectInfo) getResourceInfo(false, true);

				// setup description to obtain project location
				ProjectDescription desc = (ProjectDescription) ((ProjectDescription) description).clone();
				desc.setLocationURI(FileUtil.canonicalURI(description.getLocationURI()));
				desc.setName(getName());
				internalSetDescription(desc, false);
				// see if there potentially are already contents on disk
				final boolean hasSavedDescription = getLocalManager().hasSavedDescription(this);
				boolean hasContent = hasSavedDescription;
				//if there is no project description, there might still be content on disk
				if (!hasSavedDescription)
					hasContent = getLocalManager().hasSavedContent(this);
				try {
					// look for a description on disk
					if (hasSavedDescription) {
						updateDescription();
						//make sure the .location file is written
						workspace.getMetaArea().writePrivateDescription(this);
					} else {
						//write out the project
						writeDescription(IResource.FORCE);
					}
				} catch (CoreException e) {
					workspace.deleteResource(this);
					throw e;
				}
				// inaccessible projects have a null modification stamp.
				// set this after setting the description as #setDescription
				// updates the stamp
				info.clearModificationStamp();
				//if a project already had content on disk, mark the project as having unknown children
				if (hasContent)
					info.set(ICoreConstants.M_CHILDREN_UNKNOWN);
				workspace.getSaveManager().requestSnapshot();
			} catch (OperationCanceledException e) {
				workspace.getWorkManager().operationCanceled();
				throw e;
			} finally {
				workspace.endOperation(rule, true, Policy.subMonitorFor(monitor, Policy.endOpWork));
			}
		} finally {
			monitor.done();
		}
	}

	/* (non-Javadoc)
	 * @see IProject#delete(boolean, boolean, IProgressMonitor)
	 */
	public void delete(boolean deleteContent, boolean force, IProgressMonitor monitor) throws CoreException {
		int updateFlags = force ? IResource.FORCE : IResource.NONE;
		updateFlags |= deleteContent ? IResource.ALWAYS_DELETE_PROJECT_CONTENT : IResource.NEVER_DELETE_PROJECT_CONTENT;
		delete(updateFlags, monitor);
	}

	/* (non-Javadoc)
	 * @see IResource#delete(boolean, IProgressMonitor)
	 */
	public void delete(boolean force, IProgressMonitor monitor) throws CoreException {
		int updateFlags = force ? IResource.FORCE : IResource.NONE;
		delete(updateFlags, monitor);
	}

	public void deleteResource(boolean convertToPhantom, MultiStatus status) throws CoreException {
		super.deleteResource(convertToPhantom, status);
		// Delete the project metadata.
		workspace.getMetaArea().delete(this);
		// Clear the history store.
		clearHistory(null);
	}

	protected void fixupAfterMoveSource()  throws CoreException {
		workspace.deleteResource(this);
		// check if we deleted a preferences file 
		ProjectPreferences.deleted(this);
	}

	/*
	 *  (non-Javadoc)
	 * @see IProject#getContentTypeMatcher
	 */
	public IContentTypeMatcher getContentTypeMatcher() throws CoreException {
		return workspace.getContentDescriptionManager().getContentTypeMatcher(this);
	}

	/* (non-Javadoc)
	 * @see IContainer#getDefaultCharset(boolean)
	 */
	public String getDefaultCharset(boolean checkImplicit) {
		// non-existing resources default to parent's charset
		if (!exists())
			return checkImplicit ? ResourcesPlugin.getEncoding() : null;
		return workspace.getCharsetManager().getCharsetFor(getFullPath(), checkImplicit);
	}

	/* (non-Javadoc)
	 * @see IProject#getDescription()
	 */
	public IProjectDescription getDescription() throws CoreException {
		ResourceInfo info = getResourceInfo(false, false);
		checkAccessible(getFlags(info));
		ProjectDescription description = ((ProjectInfo) info).getDescription();
		//if the project is currently in the middle of being created, the description might not be available yet
		if (description == null)
			checkAccessible(NULL_FLAG);
		return (IProjectDescription) description.clone();
	}

	/* (non-Javadoc)
	 * @see IProject#getNature(String)
	 */
	public IProjectNature getNature(String natureID) throws CoreException {
		// Has it already been initialized?
		ProjectInfo info = (ProjectInfo) getResourceInfo(false, false);
		checkAccessible(getFlags(info));
		IProjectNature nature = info.getNature(natureID);
		if (nature == null) {
			// Not initialized yet. Does this project have the nature?
			if (!hasNature(natureID))
				return null;
			nature = workspace.getNatureManager().createNature(this, natureID);
			info.setNature(natureID, nature);
		}
		return nature;
	}

	/* (non-Javadoc)
	 * @see IResource#getParent()
	 */
	public IContainer getParent() {
		return workspace.getRoot();
	}

	/** (non-Javadoc)
	 * @see IProject#getPluginWorkingLocation(IPluginDescriptor)
	 * @deprecated
	 */
	public IPath getPluginWorkingLocation(IPluginDescriptor plugin) {
		if (plugin == null)
			return null;
		return getWorkingLocation(plugin.getUniqueIdentifier());
	}

	/* (non-Javadoc)
	 * @see IResource#getProject()
	 */
	public IProject getProject() {
		return this;
	}

	/* (non-Javadoc)
	 * @see IResource#getProjectRelativePath()
	 */
	public IPath getProjectRelativePath() {
		return Path.EMPTY;
	}

	/* (non-Javadoc)
	 * @see IResource#getRawLocation()
	 */
	public IPath getRawLocation() {
		ProjectDescription description = internalGetDescription();
		return description == null ? null : description.getLocation();
	}

	/* (non-Javadoc)
	 * @see IResource#getRawLocation()
	 */
	public URI getRawLocationURI() {
		ProjectDescription description = internalGetDescription();
		return description == null ? null : description.getLocationURI();
	}

	/* (non-Javadoc)
	 * @see IProject#getReferencedProjects()
	 */
	public IProject[] getReferencedProjects() throws CoreException {
		ResourceInfo info = getResourceInfo(false, false);
		checkAccessible(getFlags(info));
		ProjectDescription description = ((ProjectInfo) info).getDescription();
		//if the project is currently in the middle of being created, the description might not be available yet
		if (description == null)
			checkAccessible(NULL_FLAG);
		return description.getAllReferences(true);
	}

	/* (non-Javadoc)
	 * @see IProject#getReferencingProjects()
	 */
	public IProject[] getReferencingProjects() {
		IProject[] projects = workspace.getRoot().getProjects(IContainer.INCLUDE_HIDDEN);
		List result = new ArrayList(projects.length);
		for (int i = 0; i < projects.length; i++) {
			Project project = (Project) projects[i];
			if (!project.isAccessible())
				continue;
			ProjectDescription description = project.internalGetDescription();
			if (description == null)
				continue;
			IProject[] references = description.getAllReferences(false);
			for (int j = 0; j < references.length; j++)
				if (references[j].equals(this)) {
					result.add(projects[i]);
					break;
				}
		}
		return (IProject[]) result.toArray(new IProject[result.size()]);
	}

	/* (non-Javadoc)
	 * @see IResource#getType()
	 */
	public int getType() {
		return PROJECT;
	}

	/*
	 *  (non-Javadoc)
	 * @see IProject#getWorkingLocation(String)
	 */
	public IPath getWorkingLocation(String id) {
		if (id == null || !exists())
			return null;
		IPath result = workspace.getMetaArea().getWorkingLocation(this, id);
		result.toFile().mkdirs();
		return result;
	}

	/* (non-Javadoc)
	 * @see IProject#hasNature(String)
	 */
	public boolean hasNature(String natureID) throws CoreException {
		checkAccessible(getFlags(getResourceInfo(false, false)));
		// use #internal method to avoid copy but still throw an
		// exception if the resource doesn't exist.
		IProjectDescription desc = internalGetDescription();
		if (desc == null)
			checkAccessible(NULL_FLAG);
		return desc.hasNature(natureID);
	}

	/**
	 * Implements all build methods on IProject.
	 */
	protected void internalBuild(final int trigger, final String builderName, final Map args, IProgressMonitor monitor) throws CoreException {
		workspace.run(new IWorkspaceRunnable() {
			public void run(IProgressMonitor innerMonitor) throws CoreException {
				innerMonitor = Policy.monitorFor(innerMonitor);
				final ISchedulingRule rule = workspace.getRoot();
				try {
					innerMonitor.beginTask("", Policy.opWork); //$NON-NLS-1$
					try {
						workspace.prepareOperation(rule, innerMonitor);
						ResourceInfo info = getResourceInfo(false, false);
						int flags = getFlags(info);
						if (!exists(flags, true) || !isOpen(flags))
							return;
						workspace.beginOperation(true);
						workspace.aboutToBuild(Project.this, trigger);
					} finally {
						workspace.endOperation(rule, false, innerMonitor);
					}
					final ISchedulingRule buildRule = workspace.getBuildManager().getRule(Project.this, trigger, builderName, args);
					try {
						IStatus result;
						workspace.prepareOperation(buildRule, innerMonitor);
						workspace.beginOperation(true);
						result = workspace.getBuildManager().build(Project.this, trigger, builderName, args, Policy.subMonitorFor(innerMonitor, Policy.opWork));
						if (!result.isOK())
							throw new ResourceException(result);
					} finally {
						workspace.endOperation(buildRule, false, innerMonitor);
						try {
							workspace.prepareOperation(rule, innerMonitor);
							workspace.beginOperation(true);
							workspace.broadcastBuildEvent(Project.this, IResourceChangeEvent.POST_BUILD, trigger);
							//building may close the tree, so open it
							if (workspace.getElementTree().isImmutable())
								workspace.newWorkingTree();
						} finally {
							workspace.endOperation(rule, false, Policy.subMonitorFor(innerMonitor, Policy.endOpWork));
						}
					}
				} finally {
					innerMonitor.done();
				}
			}
		}, monitor);
	}

	/**
	 * Closes the project.  This is called during restore when there is a failure
	 * to read the project description.  Since it is called during workspace restore,
	 * it cannot start any operations.
	 */
	protected void internalClose() throws CoreException {
		workspace.flushBuildOrder();
		getMarkerManager().removeMarkers(this, IResource.DEPTH_INFINITE);
		// remove each member from the resource tree. 
		// DO NOT use resource.delete() as this will delete it from disk as well.
		IResource[] members = members(IContainer.INCLUDE_PHANTOMS | IContainer.INCLUDE_TEAM_PRIVATE_MEMBERS | IContainer.INCLUDE_HIDDEN);
		for (int i = 0; i < members.length; i++) {
			Resource member = (Resource) members[i];
			workspace.deleteResource(member);
		}
		// finally mark the project as closed.
		ResourceInfo info = getResourceInfo(false, true);
		info.clear(M_OPEN);
		info.clearSessionProperties();
		info.clearModificationStamp();
		info.setSyncInfo(null);
	}

	protected void internalCopy(IProjectDescription destDesc, int updateFlags, IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		try {
			String message = NLS.bind(Messages.resources_copying, getFullPath());
			monitor.beginTask(message, Policy.totalWork);
			String destName = destDesc.getName();
			IPath destPath = new Path(destName).makeAbsolute();
			Project destination = (Project) workspace.getRoot().getProject(destName);
			final ISchedulingRule rule = workspace.getRuleFactory().copyRule(this, destination);
			try {
				workspace.prepareOperation(rule, monitor);
				// The following assert method throws CoreExceptions as stated in the IProject.copy API
				// and assert for programming errors. See checkCopyRequirements for more information.
				assertCopyRequirements(destPath, IResource.PROJECT, updateFlags);
				checkDescription(destination, destDesc, false);
				workspace.broadcastEvent(LifecycleEvent.newEvent(LifecycleEvent.PRE_PROJECT_COPY, this, destination, updateFlags));

				workspace.beginOperation(true);
				getLocalManager().refresh(this, DEPTH_INFINITE, true, Policy.subMonitorFor(monitor, Policy.opWork * 20 / 100));

				// close the property store so incorrect info is not copied to the destination
				getPropertyManager().closePropertyStore(this);
				getLocalManager().getHistoryStore().closeHistoryStore(this);

				// copy the meta area for the project
				copyMetaArea(this, destination, Policy.subMonitorFor(monitor, Policy.opWork * 5 / 100));

				// copy just the project and not its children yet (tree node, properties)
				internalCopyProjectOnly(destination, Policy.subMonitorFor(monitor, Policy.opWork * 5 / 100));

				// set the description
				destination.internalSetDescription(destDesc, false);

				//create the directory for the new project
				destination.getStore().mkdir(EFS.NONE, Policy.subMonitorFor(monitor, Policy.opWork * 5 / 100));

				// call super.copy for each child (excluding project description file)
				//make it a best effort copy
				message = Messages.resources_copyProblem;
				MultiStatus problems = new MultiStatus(ResourcesPlugin.PI_RESOURCES, IResourceStatus.INTERNAL_ERROR, message, null);

				IResource[] children = members(IContainer.INCLUDE_TEAM_PRIVATE_MEMBERS | IContainer.INCLUDE_HIDDEN);
				final int childCount = children.length;
				final int childWork = childCount > 1 ? Policy.opWork * 50 / 100 / (childCount - 1) : 0;
				for (int i = 0; i < childCount; i++) {
					IResource child = children[i];
					if (!isProjectDescriptionFile(child)) {
						try {
							child.copy(destPath.append(child.getName()), updateFlags, Policy.subMonitorFor(monitor, childWork));
						} catch (CoreException e) {
							problems.merge(e.getStatus());
						}
					}
				}

				// write out the new project description to the meta area
				try {
					destination.writeDescription(IResource.FORCE);
				} catch (CoreException e) {
					try {
						destination.delete((updateFlags & IResource.FORCE) != 0, null);
					} catch (CoreException e2) {
						// ignore and rethrow the exception that got us here
					}
					throw e;
				}
				monitor.worked(Policy.opWork * 5 / 100);

				// refresh local
				monitor.subTask(Messages.resources_updating);
				getLocalManager().refresh(destination, DEPTH_INFINITE, true, Policy.subMonitorFor(monitor, Policy.opWork * 10 / 100));
				if (!problems.isOK())
					throw new ResourceException(problems);
			} catch (OperationCanceledException e) {
				workspace.getWorkManager().operationCanceled();
				throw e;
			} finally {
				workspace.endOperation(rule, true, Policy.subMonitorFor(monitor, Policy.endOpWork));
			}
		} finally {
			monitor.done();
		}
	}

	/*
	 * Copies just the project and no children. Does NOT copy the meta area.
	 */
	protected void internalCopyProjectOnly(IResource destination, IProgressMonitor monitor) throws CoreException {
		// close the property store so bogus values aren't copied to the destination
		getPropertyManager().closePropertyStore(this);
		getLocalManager().getHistoryStore().closeHistoryStore(this);
		// copy the tree and properties
		workspace.copyTree(this, destination.getFullPath(), IResource.DEPTH_ZERO, IResource.NONE, false);
		getPropertyManager().copy(this, destination, IResource.DEPTH_ZERO);

		ProjectInfo info = (ProjectInfo) ((Resource) destination).getResourceInfo(false, true);

		//clear properties, markers, and description for the new project, because they shouldn't be copied.
		info.description = null;
		info.natures = null;
		info.setMarkers(null);
		info.clearSessionProperties();
	}

	/**
	 * This is an internal helper method. This implementation is different from the API
	 * method getDescription(). This one does not check the project accessibility. It exists
	 * in order to prevent "chicken and egg" problems in places like the project creation.
	 * It may return null.
	 */
	public ProjectDescription internalGetDescription() {
		ProjectInfo info = (ProjectInfo) getResourceInfo(false, false);
		if (info == null)
			return null;
		return info.getDescription();
	}

	/**
	 * Sets this project's description to the given value.  This is the body of the
	 * corresponding API method but is needed separately since it is used
	 * during workspace restore (i.e., when you cannot do an operation)
	 */
	void internalSetDescription(IProjectDescription value, boolean incrementContentId) {
		ProjectInfo info = (ProjectInfo) getResourceInfo(false, true);
		info.setDescription((ProjectDescription) value);
		getLocalManager().setLocation(this, info, value.getLocationURI());
		if (incrementContentId) {
			info.incrementContentId();
			//if the project is not accessible, stamp will be null and should remain null
			if (info.getModificationStamp() != NULL_STAMP)
				workspace.updateModificationStamp(info);
		}
	}

	public void internalSetLocal(boolean flag, int depth) throws CoreException {
		// do nothing for projects, but call for its children
		if (depth == IResource.DEPTH_ZERO)
			return;
		if (depth == IResource.DEPTH_ONE)
			depth = IResource.DEPTH_ZERO;
		// get the children via the workspace since we know that this
		// resource exists (it is local).
		IResource[] children = getChildren(IResource.NONE);
		for (int i = 0; i < children.length; i++)
			((Resource) children[i]).internalSetLocal(flag, depth);
	}

	/* (non-Javadoc)
	 * @see IResource#isAccessible()
	 */
	public boolean isAccessible() {
		return isOpen();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.internal.resources.Resource#isDerived(int)
	 */
	public boolean isDerived(int options) {
		//projects are never derived
		return false;
	}

	public boolean isLinked(int options) {
		return false;//projects are never linked
	}

	/**
	 * @see IResource#isLocal(int)
	 * @deprecated
	 */
	public boolean isLocal(int depth) {
		// the flags parameter is ignored for projects so pass anything
		return isLocal(-1, depth);
	}

	/**
	 * @see IResource#isLocal(int)
	 * @deprecated
	 */
	public boolean isLocal(int flags, int depth) {
		// don't check the flags....projects are always local
		if (depth == DEPTH_ZERO)
			return true;
		if (depth == DEPTH_ONE)
			depth = DEPTH_ZERO;
		// get the children via the workspace since we know that this
		// resource exists (it is local).
		IResource[] children = getChildren(IResource.NONE);
		for (int i = 0; i < children.length; i++)
			if (!children[i].isLocal(depth))
				return false;
		return true;
	}

	/* (non-Javadoc)
	 * @see IProject#isNatureEnabled(String)
	 */
	public boolean isNatureEnabled(String natureId) throws CoreException {
		checkAccessible(getFlags(getResourceInfo(false, false)));
		return workspace.getNatureManager().isNatureEnabled(this, natureId);
	}

	/* (non-Javadoc)
	 * @see IProject#isOpen()
	 */
	public boolean isOpen() {
		ResourceInfo info = getResourceInfo(false, false);
		return isOpen(getFlags(info));
	}

	/* (non-Javadoc)
	 * @see IProject#isOpen()
	 */
	public boolean isOpen(int flags) {
		return flags != NULL_FLAG && ResourceInfo.isSet(flags, M_OPEN);
	}

	/**
	 * Returns true if this resource represents the project description file, and
	 * false otherwise.
	 */
	protected boolean isProjectDescriptionFile(IResource resource) {
		return resource.getType() == IResource.FILE && resource.getFullPath().segmentCount() == 2 && resource.getName().equals(IProjectDescription.DESCRIPTION_FILE_NAME);
	}

	/* (non-Javadoc)
	 * @see IProject#move(IProjectDescription, boolean, IProgressMonitor)
	 */
	public void move(IProjectDescription destination, boolean force, IProgressMonitor monitor) throws CoreException {
		Assert.isNotNull(destination);
		move(destination, force ? IResource.FORCE : IResource.NONE, monitor);
	}

	/* (non-Javadoc)
	 * @see IResource#move(IProjectDescription, int, IProgressMonitor)
	 */
	public void move(IProjectDescription description, int updateFlags, IProgressMonitor monitor) throws CoreException {
		Assert.isNotNull(description);
		monitor = Policy.monitorFor(monitor);
		try {
			String message = NLS.bind(Messages.resources_moving, getFullPath());
			monitor.beginTask(message, Policy.totalWork);
			IProject destination = workspace.getRoot().getProject(description.getName());
			final ISchedulingRule rule = workspace.getRuleFactory().moveRule(this, destination);
			try {
				workspace.prepareOperation(rule, monitor);
				// The following assert method throws CoreExceptions as stated in the IResource.move API
				// and assert for programming errors. See checkMoveRequirements for more information.
				if (!getName().equals(description.getName())) {
					IPath destPath = Path.ROOT.append(description.getName());
					assertMoveRequirements(destPath, IResource.PROJECT, updateFlags);
				}
				checkDescription(destination, description, true);
				workspace.beginOperation(true);
				message = Messages.resources_moveProblem;
				MultiStatus status = new MultiStatus(ResourcesPlugin.PI_RESOURCES, IStatus.ERROR, message, null);
				WorkManager workManager = workspace.getWorkManager();
				ResourceTree tree = new ResourceTree(getLocalManager(), workManager.getLock(), status, updateFlags);
				IMoveDeleteHook hook = workspace.getMoveDeleteHook();
				workspace.broadcastEvent(LifecycleEvent.newEvent(LifecycleEvent.PRE_PROJECT_MOVE, this, destination, updateFlags));
				int depth = 0;
				try {
					depth = workManager.beginUnprotected();
					if (!hook.moveProject(tree, this, description, updateFlags, Policy.subMonitorFor(monitor, Policy.opWork / 2)))
						tree.standardMoveProject(this, description, updateFlags, Policy.subMonitorFor(monitor, Policy.opWork / 2));
				} finally {
					workManager.endUnprotected(depth);
				}
				// Invalidate the tree for further use by clients.
				tree.makeInvalid();
				if (!tree.getStatus().isOK())
					throw new ResourceException(tree.getStatus());
			} catch (OperationCanceledException e) {
				workspace.getWorkManager().operationCanceled();
				throw e;
			} finally {
				workspace.endOperation(rule, true, Policy.subMonitorFor(monitor, Policy.endOpWork));
			}
		} finally {
			monitor.done();
		}
	}

	/* (non-Javadoc)
	 * @see IProject#open(IProgressMonitor)
	 */
	public void open(int updateFlags, IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		try {
			String msg = NLS.bind(Messages.resources_opening_1, getName());
			monitor.beginTask(msg, Policy.totalWork);
			monitor.subTask(msg);
			final ISchedulingRule rule = workspace.getRuleFactory().modifyRule(this);
			try {
				workspace.prepareOperation(rule, monitor);
				ProjectInfo info = (ProjectInfo) getResourceInfo(false, false);
				int flags = getFlags(info);
				checkExists(flags, true);
				if (isOpen(flags))
					return;

				workspace.beginOperation(true);
				// flush the build order early in case there is a problem
				workspace.flushBuildOrder();
				info = (ProjectInfo) getResourceInfo(false, true);
				info.set(M_OPEN);
				//clear the unknown children immediately to avoid background refresh
				boolean unknownChildren = info.isSet(M_CHILDREN_UNKNOWN);
				if (unknownChildren)
					info.clear(M_CHILDREN_UNKNOWN);
				// the M_USED flag is used to indicate the difference between opening a project
				// for the first time and opening it from a previous close (restoring it from disk)
				boolean used = info.isSet(M_USED);
				boolean minorIssuesDuringRestore = false;	
				if (used) {
					minorIssuesDuringRestore = workspace.getSaveManager().restore(this, Policy.subMonitorFor(monitor, Policy.opWork * 20 / 100));
				} else {
					info.set(M_USED);
					//reconcile any links in the project description
					IStatus result = reconcileLinks(info.getDescription());
					if (!result.isOK())
						throw new CoreException(result);
					workspace.updateModificationStamp(info);
					monitor.worked(Policy.opWork * 20 / 100);
				}
				startup();
				//request a refresh if the project is new and has unknown members on disk
				// or restore of the project is not fully succesfull
				if ((!used && unknownChildren) || !minorIssuesDuringRestore) {
					//refresh either in background or foreground
					if ((updateFlags & IResource.BACKGROUND_REFRESH) != 0) {
						workspace.refreshManager.refresh(this);
						monitor.worked(Policy.opWork * 80 / 100);
					} else {
						refreshLocal(IResource.DEPTH_INFINITE, Policy.subMonitorFor(monitor, Policy.opWork * 80 / 100));
					}
				}
				//creation of this project may affect overlapping resources
				workspace.getAliasManager().updateAliases(this, getStore(), IResource.DEPTH_INFINITE, monitor);
			} catch (OperationCanceledException e) {
				workspace.getWorkManager().operationCanceled();
				throw e;
			} finally {
				workspace.endOperation(rule, true, Policy.subMonitorFor(monitor, Policy.endOpWork));
			}
		} finally {
			monitor.done();
		}
	}

	/* (non-Javadoc)
	 * @see IProject#open(IProgressMonitor)
	 */
	public void open(IProgressMonitor monitor) throws CoreException {
		open(IResource.NONE, monitor);
	}

	/**
	 * The project description file has changed on disk, resulting in a changed
	 * set of linked resources.  Perform the necessary creations and deletions of
	 * links to bring the links in sync with those described in the project description.
	 * @param newDescription the new project description that may have
	 * 	changed link descriptions.
	 * @return status ok if everything went well, otherwise an ERROR multi-status 
	 * 	describing the problems encountered.
	 */
	public IStatus reconcileLinks(ProjectDescription newDescription) {
		HashMap newLinks = newDescription.getLinks();
		String msg = Messages.links_errorLinkReconcile;
		MultiStatus status = new MultiStatus(ResourcesPlugin.PI_RESOURCES, IResourceStatus.OPERATION_FAILED, msg, null);
		//walk over old linked resources and remove those that are no longer defined
		ProjectDescription oldDescription = internalGetDescription();
		if (oldDescription != null) {
			HashMap oldLinks = oldDescription.getLinks();
			if (oldLinks != null) {
				for (Iterator it = oldLinks.values().iterator(); it.hasNext();) {
					LinkDescription oldLink = (LinkDescription) it.next();
					Resource oldLinkResource = (Resource) findMember(oldLink.getProjectRelativePath());
					if (oldLinkResource == null || !oldLinkResource.isLinked())
						continue;
					LinkDescription newLink = null;
					if (newLinks != null)
						newLink = (LinkDescription) newLinks.get(oldLink.getProjectRelativePath());
					//if the new link is missing, or has different location or gender, then remove old link
					if (newLink == null || !newLink.getLocationURI().equals(oldLinkResource.getLocationURI()) || newLink.getType() != oldLinkResource.getType()) {
						try {
							oldLinkResource.delete(IResource.NONE, null);
							//refresh the resource, because removing a link can reveal a previously hidden resource in parent
							oldLinkResource.refreshLocal(IResource.DEPTH_INFINITE, null);
						} catch (CoreException e) {
							status.merge(e.getStatus());
						}
					}
				}
			}
		}
		//walk over new links and create if necessary
		if (newLinks == null)
			return status;
		//sort links to avoid creating nested links before their parents
		List sortedLinks = new ArrayList(newLinks.values());
		Collections.sort(sortedLinks);
		for (Iterator it = sortedLinks.iterator(); it.hasNext();) {
			LinkDescription newLink = (LinkDescription) it.next();
			try {
				Resource toLink = workspace.newResource(getFullPath().append(newLink.getProjectRelativePath()), newLink.getType());
				IContainer parent = toLink.getParent();
				if (parent != null && !parent.exists() && parent.getType() == FOLDER)
					((Folder) parent).ensureExists(Policy.monitorFor(null));
				toLink.createLink(newLink.getLocationURI(), IResource.REPLACE | IResource.ALLOW_MISSING_LOCAL, null);
			} catch (CoreException e) {
				status.merge(e.getStatus());
			}
		}
		return status;
	}

	/* (non-Javadoc)
	 * @see IProject#setDescription(IProjectDescription, int, IProgressMonitor)
	 */
	public void setDescription(IProjectDescription description, int updateFlags, IProgressMonitor monitor) throws CoreException {
		// FIXME - update flags should be honored:
		//    KEEP_HISTORY means capture .project file in local history
		//    FORCE means overwrite any existing .project file 
		monitor = Policy.monitorFor(monitor);
		try {
			monitor.beginTask(Messages.resources_setDesc, Policy.totalWork);
			ISchedulingRule rule = null;
			if ((updateFlags & IResource.AVOID_NATURE_CONFIG) != 0)
				rule = workspace.getRuleFactory().modifyRule(this);
			else
				rule = workspace.getRoot();		
			try {
				//need to use root rule because nature configuration calls third party code
				workspace.prepareOperation(rule, monitor);
				ResourceInfo info = getResourceInfo(false, false);
				checkAccessible(getFlags(info));
				//if nothing has changed, we don't need to do anything
				ProjectDescription oldDescription = internalGetDescription();
				ProjectDescription newDescription = (ProjectDescription) description;
				boolean hasPublicChanges = oldDescription.hasPublicChanges(newDescription);
				boolean hasPrivateChanges = oldDescription.hasPrivateChanges(newDescription);
				if (!hasPublicChanges && !hasPrivateChanges)
					return;
				checkDescription(this, newDescription, false);
				//If we're out of sync and !FORCE, then fail.
				//If the file is missing, we want to write the new description then throw an exception.
				boolean hadSavedDescription = true;
				if (((updateFlags & IResource.FORCE) == 0)) {
					hadSavedDescription = getLocalManager().hasSavedDescription(this);
					if (hadSavedDescription && !getLocalManager().isDescriptionSynchronized(this)) {
						String message = NLS.bind(Messages.resources_projectDescSync, getName());
						throw new ResourceException(IResourceStatus.OUT_OF_SYNC_LOCAL, getFullPath(), message, null);
					}
				}
				//see if we have an old .prj file
				if (!hadSavedDescription)
					hadSavedDescription = workspace.getMetaArea().hasSavedProject(this);
				workspace.broadcastEvent(LifecycleEvent.newEvent(LifecycleEvent.PRE_PROJECT_CHANGE, this));
				workspace.beginOperation(true);
				MultiStatus status = basicSetDescription(newDescription, updateFlags);
				if (hadSavedDescription && !status.isOK())
					throw new CoreException(status);
				//write the new description to the .project file
				writeDescription(oldDescription, updateFlags, hasPublicChanges, hasPrivateChanges);
				//increment the content id even for private changes
				info = getResourceInfo(false, true);
				info.incrementContentId();
				workspace.updateModificationStamp(info);
				if (!hadSavedDescription) {
					String msg = NLS.bind(Messages.resources_missingProjectMetaRepaired, getName());
					status.merge(new ResourceStatus(IResourceStatus.MISSING_DESCRIPTION_REPAIRED, getFullPath(), msg));
				}
				if (!status.isOK())
					throw new CoreException(status);
			} finally {
				workspace.endOperation(rule, true, Policy.subMonitorFor(monitor, Policy.endOpWork));
			}
		} finally {
			monitor.done();
		}
	}

	/* (non-Javadoc)
	 * @see IProject#setDescription(IProjectDescription, IProgressMonitor)
	 */
	public void setDescription(IProjectDescription description, IProgressMonitor monitor) throws CoreException {
		// funnel all operations to central method
		setDescription(description, IResource.KEEP_HISTORY, monitor);
	}

	/**
	 * Restore the non-persisted state for the project.  For example, read and set 
	 * the description from the local meta area.  Also, open the property store etc.
	 * This method is used when an open project is restored and so emulates
	 * the behaviour of open().
	 */
	protected void startup() throws CoreException {
		if (!isOpen())
			return;
		workspace.broadcastEvent(LifecycleEvent.newEvent(LifecycleEvent.PRE_PROJECT_OPEN, this));
	}

	/* (non-Javadoc)
	 * @see IResource#touch(IProgressMonitor)
	 */
	public void touch(IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		try {
			String message = NLS.bind(Messages.resources_touch, getFullPath());
			monitor.beginTask(message, Policy.totalWork);
			final ISchedulingRule rule = workspace.getRuleFactory().modifyRule(this);
			try {
				workspace.prepareOperation(rule, monitor);
				workspace.broadcastEvent(LifecycleEvent.newEvent(LifecycleEvent.PRE_PROJECT_CHANGE, this));
				workspace.beginOperation(true);
				super.touch(Policy.subMonitorFor(monitor, Policy.opWork));
			} catch (OperationCanceledException e) {
				workspace.getWorkManager().operationCanceled();
				throw e;
			} finally {
				workspace.endOperation(rule, true, Policy.subMonitorFor(monitor, Policy.endOpWork));
			}
		} finally {
			monitor.done();
		}
	}

	/**
	 * The project description file on disk is better than the description in memory.  
	 * Make sure the project description in memory is synchronized with the 
	 * description file contents.
	 */
	protected void updateDescription() throws CoreException {
		if (ProjectDescription.isWriting)
			return;
		ProjectDescription.isReading = true;
		try {
			workspace.broadcastEvent(LifecycleEvent.newEvent(LifecycleEvent.PRE_PROJECT_CHANGE, this));
			ProjectDescription description = getLocalManager().read(this, false);
			//links can only be created if the project is open
			IStatus result = null;
			if (isOpen())
				result = reconcileLinks(description);
			internalSetDescription(description, true);
			if (result != null && !result.isOK())
				throw new CoreException(result);
		} finally {
			ProjectDescription.isReading = false;
		}
	}

	/**
	 * Writes the project's current description file to disk.
	 */
	public void writeDescription(int updateFlags) throws CoreException {
		writeDescription(internalGetDescription(), updateFlags, true, true);
	}

	/**
	 * Writes the project description file to disk.  This is the only method
	 * that should ever be writing the description, because it ensures that
	 * the description isn't then immediately discovered as an incoming
	 * change and read back from disk.
	 * @param description The description to write
	 * @param updateFlags The write operation update flags
	 * @param hasPublicChanges Whether the public sections of the description have changed
	 * @param hasPrivateChanges Whether the private sections of the description have changed
	 * @exception CoreException On failure to write the description
	 */
	public void writeDescription(IProjectDescription description, int updateFlags, boolean hasPublicChanges, boolean hasPrivateChanges) throws CoreException {
		if (ProjectDescription.isReading)
			return;
		ProjectDescription.isWriting = true;
		try {
			getLocalManager().internalWrite(this, description, updateFlags, hasPublicChanges, hasPrivateChanges);
		} finally {
			ProjectDescription.isWriting = false;
		}
	}
}
