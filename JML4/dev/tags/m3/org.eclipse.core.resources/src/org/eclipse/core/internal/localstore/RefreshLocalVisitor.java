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
package org.eclipse.core.internal.localstore;

import org.eclipse.core.internal.resources.*;
import org.eclipse.core.internal.utils.Messages;
import org.eclipse.core.internal.utils.Policy;
import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.*;
import org.eclipse.osgi.util.NLS;

//
/**
 * Visits a unified tree, and synchronizes the file system with the
 * resource tree.  After the visit is complete, the file system will
 * be synchronized with the workspace tree with respect to
 * resource existence, gender, and timestamp.
 */
public class RefreshLocalVisitor implements IUnifiedTreeVisitor, ILocalStoreConstants {
	/** control constants */
	protected static final int RL_UNKNOWN = 0;
	protected static final int RL_IN_SYNC = 1;
	protected static final int RL_NOT_IN_SYNC = 2;

	/*
	 * Fields for progress monitoring algorithm.
	 * Initially, give progress for every 4 resources, double
	 * this value at halfway point, then reset halfway point
	 * to be half of remaining work.  (this gives an infinite
	 * series that converges at total work after an infinite
	 * number of resources).
	 */
	public static final int TOTAL_WORK = 250;
	private int currentIncrement = 4;
	private int halfWay = TOTAL_WORK / 2;
	private int nextProgress = currentIncrement;
	private int worked = 0;

	protected MultiStatus errors;
	protected IProgressMonitor monitor;
	protected boolean resourceChanged;
	protected Workspace workspace;

	public RefreshLocalVisitor(IProgressMonitor monitor) {
		this.monitor = monitor;
		workspace = (Workspace) ResourcesPlugin.getWorkspace();
		resourceChanged = false;
		String msg = Messages.resources_errorMultiRefresh;
		errors = new MultiStatus(ResourcesPlugin.PI_RESOURCES, IResourceStatus.FAILED_READ_LOCAL, msg, null);
	}

	/**
	 * This method has the same implementation as resourceChanged but as they are different
	 * cases, we prefer to use different methods.
	 */
	protected void contentAdded(UnifiedTreeNode node, Resource target) {
		resourceChanged(node, target);
	}

	protected void createResource(UnifiedTreeNode node, Resource target) throws CoreException {
		ResourceInfo info = target.getResourceInfo(false, false);
		int flags = target.getFlags(info);
		if (target.exists(flags, false))
			return;
		/* make sure target's parent exists */
		if (node.getLevel() == 0) {
			IContainer parent = target.getParent();
			if (parent.getType() == IResource.FOLDER)
				((Folder) target.getParent()).ensureExists(monitor);
		}
		/* Use the basic file creation protocol since we don't want to create any content on disk. */
		info = workspace.createResource(target, false);
		/* Mark this resource as having unknown children */
		info.set(ICoreConstants.M_CHILDREN_UNKNOWN);
		target.getLocalManager().updateLocalSync(info, node.getLastModified());
	}

	protected void deleteResource(UnifiedTreeNode node, Resource target) throws CoreException {
		ResourceInfo info = target.getResourceInfo(false, false);
		int flags = target.getFlags(info);
		//don't delete linked resources
		if (ResourceInfo.isSet(flags, ICoreConstants.M_LINK)) {
			//just clear local sync info
			info = target.getResourceInfo(false, true);
			//handle concurrent deletion
			if (info != null)
				info.clearModificationStamp();
			return;
		}
		if (target.exists(flags, false))
			target.deleteResource(true, errors);
		node.setExistsWorkspace(false);
	}

	protected void fileToFolder(UnifiedTreeNode node, Resource target) throws CoreException {
		ResourceInfo info = target.getResourceInfo(false, false);
		int flags = target.getFlags(info);
		if (target.exists(flags, true)) {
			target = (Folder) ((File) target).changeToFolder();
		} else {
			if (!target.exists(flags, false)) {
				target = (Resource) workspace.getRoot().getFolder(target.getFullPath());
				// Use the basic file creation protocol since we don't want to create any content on disk.
				workspace.createResource(target, false);
			}
		}
		node.setResource(target);
		info = target.getResourceInfo(false, true);
		target.getLocalManager().updateLocalSync(info, node.getLastModified());
	}

	protected void folderToFile(UnifiedTreeNode node, Resource target) throws CoreException {
		ResourceInfo info = target.getResourceInfo(false, false);
		int flags = target.getFlags(info);
		if (target.exists(flags, true))
			target = (File) ((Folder) target).changeToFile();
		else {
			if (!target.exists(flags, false)) {
				target = (Resource) workspace.getRoot().getFile(target.getFullPath());
				// Use the basic file creation protocol since we don't want to 
				// create any content on disk.
				workspace.createResource(target, false);
			}
		}
		node.setResource(target);
		info = target.getResourceInfo(false, true);
		target.getLocalManager().updateLocalSync(info, node.getLastModified());
	}

	/**
	 * Returns the status of the nodes visited so far.  This will be a multi-status
	 * that describes all problems that have occurred, or an OK status if everything
	 * went smoothly.  
	 */
	public IStatus getErrorStatus() {
		return errors;
	}

	protected void makeLocal(UnifiedTreeNode node, Resource target) {
		ResourceInfo info = target.getResourceInfo(false, true);
		if (info != null)
			target.getLocalManager().updateLocalSync(info, node.getLastModified());
	}

	/**
	 * Refreshes the parent of a resource currently being synchronized.
	 */
	protected void refresh(Container parent) throws CoreException {
		parent.getLocalManager().refresh(parent, IResource.DEPTH_ZERO, false, null);
	}

	protected void resourceChanged(UnifiedTreeNode node, Resource target) {
		ResourceInfo info = target.getResourceInfo(false, true);
		if (info == null)
			return;
		target.getLocalManager().updateLocalSync(info, node.getLastModified());
		info.incrementContentId();
		// forget content-related caching flags		
		info.clear(ICoreConstants.M_CONTENT_CACHE);
		workspace.updateModificationStamp(info);
	}

	public boolean resourcesChanged() {
		return resourceChanged;
	}

	/**
	 * deletion or creation -- Returns:
	 * 	- RL_IN_SYNC - the resource is in-sync with the file system
	 * 	- RL_NOT_IN_SYNC - the resource is not in-sync with file system
	 * 	- RL_UNKNOWN - couldn't determine the sync status for this resource 
	 */
	protected int synchronizeExistence(UnifiedTreeNode node, Resource target) throws CoreException {
		if (node.existsInWorkspace()) {
			if (!node.existsInFileSystem()) {
				//non-local files are always in sync
				if (target.isLocal(IResource.DEPTH_ZERO)) {
					deleteResource(node, target);
					resourceChanged = true;
					return RL_NOT_IN_SYNC;
				}
				return RL_IN_SYNC;
			}
		} else {
			// do we have a gender variant in the workspace?
			IResource genderVariant = workspace.getRoot().findMember(target.getFullPath());
			if (genderVariant != null)
				return RL_UNKNOWN;
			if (node.existsInFileSystem()) {
				Container parent = (Container) target.getParent();
				if (!parent.exists()) {
					refresh(parent);
					if (!parent.exists())
						return RL_NOT_IN_SYNC;
				}
				if (!target.getName().equals(node.getLocalName()))
					return RL_IN_SYNC;
				if (!Workspace.caseSensitive && node.getLevel() == 0) {
					// do we have any alphabetic variants in the workspace?
					IResource variant = target.findExistingResourceVariant(target.getFullPath());
					if (variant != null) {
						deleteResource(node, ((Resource) variant));
						createResource(node, target);
						resourceChanged = true;
						return RL_NOT_IN_SYNC;
					}
				}
				createResource(node, target);
				resourceChanged = true;
				return RL_NOT_IN_SYNC;
			}
		}
		return RL_UNKNOWN;
	}

	/**
	 * gender change -- Returns true if gender was in sync.
	 */
	protected boolean synchronizeGender(UnifiedTreeNode node, Resource target) throws CoreException {
		if (!node.existsInWorkspace()) {
			//may be an existing resource in the workspace of different gender
			IResource genderVariant = workspace.getRoot().findMember(target.getFullPath());
			if (genderVariant != null)
				target = (Resource) genderVariant;
		}
		if (target.getType() == IResource.FILE) {
			if (node.isFolder()) {
				fileToFolder(node, target);
				resourceChanged = true;
				return false;
			}
		} else {
			if (!node.isFolder()) {
				folderToFile(node, target);
				resourceChanged = true;
				return false;
			}
		}
		return true;
	}

	/**
	 * lastModified
	 */
	protected void synchronizeLastModified(UnifiedTreeNode node, Resource target) {
		if (target.isLocal(IResource.DEPTH_ZERO))
			resourceChanged(node, target);
		else
			contentAdded(node, target);
		resourceChanged = true;
	}

	public boolean visit(UnifiedTreeNode node) throws CoreException {
		Policy.checkCanceled(monitor);
		try {
			Resource target = (Resource) node.getResource();
			int targetType = target.getType();
			if (targetType == IResource.PROJECT)
				return true;
			if (node.existsInWorkspace() && node.existsInFileSystem()) {
				/* for folders we only care about updating local status */
				if (targetType == IResource.FOLDER && node.isFolder()) {
					// if not local, mark as local
					if (!target.isLocal(IResource.DEPTH_ZERO))
						makeLocal(node, target);
					ResourceInfo info = target.getResourceInfo(false, false);
					if (info != null && info.getModificationStamp() != IResource.NULL_STAMP)
						return true;
				}
				/* compare file last modified */
				if (targetType == IResource.FILE && !node.isFolder()) {
					ResourceInfo info = target.getResourceInfo(false, false);
					if (info != null && info.getModificationStamp() != IResource.NULL_STAMP && info.getLocalSyncInfo() == node.getLastModified())
						return true;
				}
			} else {
				if (node.existsInFileSystem() && !Path.EMPTY.isValidSegment(node.getLocalName())) {
					String message = NLS.bind(Messages.resources_invalidResourceName, node.getLocalName());
					errors.merge(new ResourceStatus(IResourceStatus.INVALID_RESOURCE_NAME, message));
					return false;
				}
				int state = synchronizeExistence(node, target);
				if (state == RL_IN_SYNC || state == RL_NOT_IN_SYNC) {
					if (targetType == IResource.FILE) {
						try {
							((File) target).updateMetadataFiles();
						} catch (CoreException e) {
							errors.merge(e.getStatus());
						}
					}
					return true;
				}
			}
			if (synchronizeGender(node, target))
				synchronizeLastModified(node, target);
			if (targetType == IResource.FILE) {
				try {
					((File) target).updateMetadataFiles();
				} catch (CoreException e) {
					errors.merge(e.getStatus());
				}
			}
			return true;
		} finally {
			if (--nextProgress <= 0) {
				//we have exhausted the current increment, so report progress
				monitor.worked(1);
				worked++;
				if (worked >= halfWay) {
					//we have passed the current halfway point, so double the
					//increment and reset the halfway point.
					currentIncrement *= 2;
					halfWay += (TOTAL_WORK - halfWay) / 2;
				}
				//reset the progress counter to another full increment
				nextProgress = currentIncrement;
			}
		}
	}
}
