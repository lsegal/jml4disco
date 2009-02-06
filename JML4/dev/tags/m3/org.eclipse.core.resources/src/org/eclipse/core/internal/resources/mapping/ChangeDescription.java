/*******************************************************************************
 * Copyright (c) 2006 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.core.internal.resources.mapping;

import java.util.*;
import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.IPath;

/**
 * A description of the changes found in a delta
 */
public class ChangeDescription {

	private List addedRoots = new ArrayList();
	private List changedFiles = new ArrayList();
	private List closedProjects = new ArrayList();
	private List copiedRoots = new ArrayList();
	private List movedRoots = new ArrayList();
	private List removedRoots = new ArrayList();

	private IResource createSourceResource(IResourceDelta delta) {
		IPath sourcePath = delta.getMovedFromPath();
		IResource resource = delta.getResource();
		IWorkspaceRoot wsRoot = ResourcesPlugin.getWorkspace().getRoot();
		switch (resource.getType()) {
			case IResource.PROJECT :
				return wsRoot.getProject(sourcePath.segment(0));
			case IResource.FOLDER :
				return wsRoot.getFolder(sourcePath);
			case IResource.FILE :
				return wsRoot.getFile(sourcePath);
		}
		return null;
	}

	private void ensureResourceCovered(IResource resource, List list) {
		IPath path = resource.getFullPath();
		for (Iterator iter = list.iterator(); iter.hasNext();) {
			IResource root = (IResource) iter.next();
			if (root.getFullPath().isPrefixOf(path)) {
				return;
			}
		}
		list.add(resource);
	}

	public IResource[] getRootResources() {
		Set result = new HashSet();
		result.addAll(addedRoots);
		result.addAll(changedFiles);
		result.addAll(closedProjects);
		result.addAll(copiedRoots);
		result.addAll(movedRoots);
		result.addAll(removedRoots);
		return (IResource[]) result.toArray(new IResource[result.size()]);
	}

	private void handleAdded(IResourceDelta delta) {
		if ((delta.getFlags() & IResourceDelta.MOVED_FROM) != 0) {
			handleMove(delta);
		} else if ((delta.getFlags() & IResourceDelta.COPIED_FROM) != 0) {
			handleCopy(delta);
		} else {
			ensureResourceCovered(delta.getResource(), addedRoots);
		}
	}

	private void handleChange(IResourceDelta delta) {
		if ((delta.getFlags() & IResourceDelta.REPLACED) != 0) {
			// A replace was added in place of a removed resource
			handleAdded(delta);
		} else if (delta.getResource().getType() == IResource.FILE) {
			ensureResourceCovered(delta.getResource(), changedFiles);
		}
	}

	private void handleCopy(IResourceDelta delta) {
		if ((delta.getFlags() & IResourceDelta.COPIED_FROM) != 0) {
			IResource source = createSourceResource(delta);
			ensureResourceCovered(source, copiedRoots);
		}
	}

	private void handleMove(IResourceDelta delta) {
		if ((delta.getFlags() & IResourceDelta.MOVED_TO) != 0) {
			movedRoots.add(delta.getResource());
		} else if ((delta.getFlags() & IResourceDelta.MOVED_FROM) != 0) {
			IResource source = createSourceResource(delta);
			ensureResourceCovered(source, movedRoots);
		}
	}

	private void handleRemoved(IResourceDelta delta) {
		if ((delta.getFlags() & IResourceDelta.OPEN) != 0) {
			closedProjects.add(delta.getResource());
		} else if ((delta.getFlags() & IResourceDelta.MOVED_TO) != 0) {
			handleMove(delta);
		} else {
			ensureResourceCovered(delta.getResource(), removedRoots);
		}
	}

	/**
	 * Record the change and return whether any child changes should be visited.
	 * @param delta the change
	 * @return whether any child changes should be visited
	 */
	public boolean recordChange(IResourceDelta delta) {
		switch (delta.getKind()) {
			case IResourceDelta.ADDED :
				handleAdded(delta);
				return true; // Need to traverse children to look  for moves or other changes under added roots
			case IResourceDelta.REMOVED :
				handleRemoved(delta);
				// No need to look for further changes under a remove (such as moves).
				// Changes will be discovered in corresponding destination delta
				return false;
			case IResourceDelta.CHANGED :
				handleChange(delta);
				return true;
		}
		return true;
	}

}
