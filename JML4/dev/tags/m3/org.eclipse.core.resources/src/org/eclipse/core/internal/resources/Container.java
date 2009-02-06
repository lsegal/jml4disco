/*******************************************************************************
 * Copyright (c) 2000, 2007 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.core.internal.resources;

import java.util.*;
import org.eclipse.core.internal.localstore.IHistoryStore;
import org.eclipse.core.internal.utils.*;
import org.eclipse.core.internal.watson.*;
import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.*;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.osgi.util.NLS;

public abstract class Container extends Resource implements IContainer {
	protected Container(IPath path, Workspace container) {
		super(path, container);
	}

	/**
	 * Converts this resource and all its children into phantoms by modifying
	 * their resource infos in-place.
	 */
	public void convertToPhantom() throws CoreException {
		if (isPhantom())
			return;
		super.convertToPhantom();
		IResource[] members = members(IContainer.INCLUDE_PHANTOMS | IContainer.INCLUDE_TEAM_PRIVATE_MEMBERS | IContainer.INCLUDE_HIDDEN);
		for (int i = 0; i < members.length; i++)
			((Resource) members[i]).convertToPhantom();
	}

	/* (non-Javadoc)
	 * @see IContainer#exists(IPath)
	 */
	public boolean exists(IPath childPath) {
		return workspace.getResourceInfo(getFullPath().append(childPath), false, false) != null;
	}

	/* (non-Javadoc)
	 * @see IContainer#findMember(String)
	 */
	public IResource findMember(String name) {
		return findMember(name, false);
	}

	/* (non-Javadoc)
	 * @see IContainer#findMember(String, boolean)
	 */
	public IResource findMember(String name, boolean phantom) {
		IPath childPath = getFullPath().append(name);
		ResourceInfo info = workspace.getResourceInfo(childPath, phantom, false);
		return info == null ? null : workspace.newResource(childPath, info.getType());
	}

	/* (non-Javadoc)
	 * @see IContainer#findMember(IPath)
	 */
	public IResource findMember(IPath childPath) {
		return findMember(childPath, false);
	}

	/* (non-Javadoc)
	 * @see IContainer#findMember(IPath)
	 */
	public IResource findMember(IPath childPath, boolean phantom) {
		childPath = getFullPath().append(childPath);
		ResourceInfo info = workspace.getResourceInfo(childPath, phantom, false);
		return (info == null) ? null : workspace.newResource(childPath, info.getType());
	}

	protected void fixupAfterMoveSource() throws CoreException {
		super.fixupAfterMoveSource();
		if (!synchronizing(getResourceInfo(true, false)))
			return;
		IResource[] members = members(IContainer.INCLUDE_PHANTOMS | IContainer.INCLUDE_TEAM_PRIVATE_MEMBERS | IContainer.INCLUDE_HIDDEN);
		for (int i = 0; i < members.length; i++)
			((Resource) members[i]).fixupAfterMoveSource();
	}

	protected IResource[] getChildren(int memberFlags) {
		IPath[] children = null;
		try {
			children = workspace.tree.getChildren(path);
		} catch (IllegalArgumentException e) {
			//concurrency problem: the container has been deleted by another 
			//thread during this call.  Just return empty children set
		}
		if (children == null || children.length == 0)
			return ICoreConstants.EMPTY_RESOURCE_ARRAY;
		Resource[] result = new Resource[children.length];
		int found = 0;
		for (int i = 0; i < children.length; i++) {
			ResourceInfo info = workspace.getResourceInfo(children[i], true, false);
			if (info != null && isMember(info.getFlags(), memberFlags))
				result[found++] = workspace.newResource(children[i], info.getType());
		}
		if (found == result.length)
			return result;
		Resource[] trimmedResult = new Resource[found];
		System.arraycopy(result, 0, trimmedResult, 0, found);
		return trimmedResult;
	}

	/* (non-Javadoc)
	 * @see IFolder#getFile(String) and IProject#getFile(String)
	 */
	public IFile getFile(String name) {
		return (IFile) workspace.newResource(getFullPath().append(name), FILE);
	}

	/* (non-Javadoc)
	 * @see IContainer#getFile(IPath)
	 */
	public IFile getFile(IPath childPath) {
		return (IFile) workspace.newResource(getFullPath().append(childPath), FILE);
	}

	/* (non-Javadoc)
	 * @see IFolder#getFolder(String) and IProject#getFolder(String)
	 */
	public IFolder getFolder(String name) {
		return (IFolder) workspace.newResource(getFullPath().append(name), FOLDER);
	}

	/* (non-Javadoc)
	 * @see IContainer#getFolder(IPath)
	 */
	public IFolder getFolder(IPath childPath) {
		return (IFolder) workspace.newResource(getFullPath().append(childPath), FOLDER);
	}

	/**
	 * @deprecated
	 */
	public boolean isLocal(int flags, int depth) {
		if (!super.isLocal(flags, depth))
			return false;
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
	 * @see IContainer#members()
	 */
	public IResource[] members() throws CoreException {
		// forward to central method
		return members(IResource.NONE);
	}

	/* (non-Javadoc)
	 * @see IContainer#members(boolean)
	 */
	public IResource[] members(boolean phantom) throws CoreException {
		// forward to central method
		return members(phantom ? INCLUDE_PHANTOMS : IResource.NONE);
	}

	/* (non-Javadoc)
	 * @see IContainer#members(int)
	 */
	public IResource[] members(int memberFlags) throws CoreException {
		final boolean phantom = (memberFlags & INCLUDE_PHANTOMS) != 0;
		ResourceInfo info = getResourceInfo(phantom, false);
		checkAccessible(getFlags(info));
		//if children are currently unknown, ask for immediate refresh
		if (info.isSet(ICoreConstants.M_CHILDREN_UNKNOWN))
			workspace.refreshManager.refresh(this);
		return getChildren(memberFlags);
	}

	/* (non-Javadoc)
	 * @see IContainer#getDefaultCharset()
	 */
	public String getDefaultCharset() throws CoreException {
		return getDefaultCharset(true);
	}

	/* (non-Javadoc)
	 * @see IContainer#findDeletedMembersWithHistory(int, IProgressMonitor)
	 */
	public IFile[] findDeletedMembersWithHistory(int depth, IProgressMonitor monitor) {
		IHistoryStore historyStore = getLocalManager().getHistoryStore();
		IPath basePath = getFullPath();
		IWorkspaceRoot root = getWorkspace().getRoot();
		Set deletedFiles = new HashSet();

		if (depth == IResource.DEPTH_ZERO) {
			// this folder might have been a file in a past life
			if (historyStore.getStates(basePath, monitor).length > 0) {
				IFile file = root.getFile(basePath);
				if (!file.exists()) {
					deletedFiles.add(file);
				}
			}
		} else {
			Set allFilePaths = historyStore.allFiles(basePath, depth, monitor);
			// convert IPaths to IFiles keeping only files that no longer exist
			for (Iterator it = allFilePaths.iterator(); it.hasNext();) {
				IPath filePath = (IPath) it.next();
				IFile file = root.getFile(filePath);
				if (!file.exists()) {
					deletedFiles.add(file);
				}
			}
		}
		return (IFile[]) deletedFiles.toArray(new IFile[deletedFiles.size()]);
	}

	/** (non-Javadoc)
	 * @see IContainer#setDefaultCharset(String)
	 * @deprecated Replaced by {@link #setDefaultCharset(String, IProgressMonitor)} which 
	 * 	is a workspace operation and reports changes in resource deltas.
	 */
	public void setDefaultCharset(String charset) throws CoreException {
		ResourceInfo info = getResourceInfo(false, false);
		checkAccessible(getFlags(info));
		workspace.getCharsetManager().setCharsetFor(getFullPath(), charset);
	}

	/* (non-Javadoc)
	 * @see IContainer#setDefaultCharset(String, IProgressMonitor)
	 */
	public void setDefaultCharset(String newCharset, IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		try {
			String message = NLS.bind(Messages.resources_settingDefaultCharsetContainer, getFullPath());
			monitor.beginTask(message, Policy.totalWork);
			// need to get the project as a scheduling rule because we might be 
			// creating a new folder/file to hold the project settings
			final ISchedulingRule rule = workspace.getRuleFactory().charsetRule(this);
			try {
				workspace.prepareOperation(rule, monitor);
				checkAccessible(getFlags(getResourceInfo(false, false)));
				workspace.beginOperation(true);
				workspace.getCharsetManager().setCharsetFor(getFullPath(), newCharset);
				// now propagate the changes to all children inheriting their setting from this container
				IElementContentVisitor visitor = new IElementContentVisitor() {
					boolean visitedRoot = false;

					public boolean visitElement(ElementTree tree, IPathRequestor requestor, Object elementContents) {
						if (elementContents == null)
							return false;
						IPath nodePath = requestor.requestPath();
						// we will always generate an event at least for the root of the sub tree
						// (skip visiting the root because we already have set the charset above and
						// that is the condition we are checking later)
						if (!visitedRoot) {
							visitedRoot = true;
							ResourceInfo info = workspace.getResourceInfo(nodePath, false, true);
							if (info == null)
								return false;
							info.incrementCharsetGenerationCount();
							return true;
						}						
						// does it already have an encoding explicitly set?
						if (workspace.getCharsetManager().getCharsetFor(nodePath, false) != null)
							return false;
						ResourceInfo info = workspace.getResourceInfo(nodePath, false, true);
						if (info == null)
							return false;
						info.incrementCharsetGenerationCount();
						return true;
					}
				};
				try {
					new ElementTreeIterator(workspace.getElementTree(), getFullPath()).iterate(visitor);
				} catch (WrappedRuntimeException e) {
					throw (CoreException) e.getTargetException();
				}
				monitor.worked(Policy.opWork);
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
}
