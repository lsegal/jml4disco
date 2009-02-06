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

import org.eclipse.core.internal.watson.IPathRequestor;
import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.QualifiedName;

/**
 * Implements a resource proxy given a path requestor and the resource
 * info of the resource currently being visited.
 */
public class ResourceProxy implements IResourceProxy, ICoreConstants {
	protected final Workspace workspace = (Workspace) ResourcesPlugin.getWorkspace();
	protected IPathRequestor requestor;
	protected ResourceInfo info;

	//cached info
	protected IPath fullPath;
	protected IResource resource;

	/**
	 * @see org.eclipse.core.resources.IResourceProxy#getModificationStamp()
	 */
	public long getModificationStamp() {
		return info.getModificationStamp();
	}

	public String getName() {
		return requestor.requestName();
	}

	public Object getSessionProperty(QualifiedName key) {
		return info.getSessionProperty(key);
	}

	public int getType() {
		return info.getType();
	}

	/**
	 * @see org.eclipse.core.resources.IResourceProxy#isAccessible()
	 */
	public boolean isAccessible() {
		int flags = info.getFlags();
		if (info.getType() == IResource.PROJECT)
			return flags != NULL_FLAG && ResourceInfo.isSet(flags, M_OPEN);
		return flags != NULL_FLAG;
	}

	/**
	 * @see org.eclipse.core.resources.IResourceProxy#isDerived()
	 */
	public boolean isDerived() {
		int flags = info.getFlags();
		return flags != NULL_FLAG && ResourceInfo.isSet(flags, M_DERIVED);
	}

	/**
	 * @see org.eclipse.core.resources.IResourceProxy#isLinked()
	 */
	public boolean isLinked() {
		int flags = info.getFlags();
		return flags != NULL_FLAG && ResourceInfo.isSet(flags, M_LINK);
	}

	/**
	 * @see org.eclipse.core.resources.IResourceProxy#isPhantom()
	 */
	public boolean isPhantom() {
		int flags = info.getFlags();
		return flags != NULL_FLAG && ResourceInfo.isSet(flags, M_PHANTOM);
	}

	/**
	 * @see org.eclipse.core.resources.IResourceProxy#isTeamPrivateMember()
	 */
	public boolean isTeamPrivateMember() {
		int flags = info.getFlags();
		return flags != NULL_FLAG && ResourceInfo.isSet(flags, M_TEAM_PRIVATE_MEMBER);
	}
	
	/**
	 * @see org.eclipse.core.resources.IResourceProxy#isHidden()
	 */
	public boolean isHidden() {
		int flags = info.getFlags();
		return flags != NULL_FLAG && ResourceInfo.isSet(flags, M_HIDDEN);
	}

	/**
	 * @see org.eclipse.core.resources.IResourceProxy#requestFullPath()
	 */
	public IPath requestFullPath() {
		if (fullPath == null)
			fullPath = requestor.requestPath();
		return fullPath;
	}

	/**
	 * @see org.eclipse.core.resources.IResourceProxy#requestResource()
	 */
	public IResource requestResource() {
		if (resource == null)
			resource = workspace.newResource(requestFullPath(), info.getType());
		return resource;
	}

	protected void reset() {
		fullPath = null;
		resource = null;
	}
}
