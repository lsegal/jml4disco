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

import java.io.*;
import org.eclipse.core.internal.localstore.IHistoryStore;
import org.eclipse.core.internal.utils.Messages;
import org.eclipse.core.internal.utils.UniversalUniqueIdentifier;
import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.*;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentTypeManager;
import org.eclipse.osgi.util.NLS;

public class FileState extends PlatformObject implements IFileState {
	private static final IWorkspace workspace = ResourcesPlugin.getWorkspace();
	protected long lastModified;
	protected UniversalUniqueIdentifier uuid;
	protected IHistoryStore store;
	protected IPath fullPath;

	public FileState(IHistoryStore store, IPath fullPath, long lastModified, UniversalUniqueIdentifier uuid) {
		this.store = store;
		this.lastModified = lastModified;
		this.uuid = uuid;
		this.fullPath = fullPath;
	}

	/* (non-Javadoc)
	 * @see IFileState#exists()
	 */
	public boolean exists() {
		return store.exists(this);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.IEncodedStorage#getCharset()
	 */
	public String getCharset() throws CoreException {
		// if there is an existing file at this state's path, use the encoding of that file
		IResource file = workspace.getRoot().findMember(fullPath);
		if (file != null && file.getType() == IResource.FILE)
			return ((IFile)file).getCharset();
		
		// tries to obtain a description for the file contents
		IContentTypeManager contentTypeManager = Platform.getContentTypeManager();
		InputStream contents = new BufferedInputStream(getContents());
		boolean failed = false;
		try {
			IContentDescription description = contentTypeManager.getDescriptionFor(contents, getName(), new QualifiedName[] {IContentDescription.CHARSET});
			return description == null ? null : description.getCharset();
		} catch (IOException e) {
			failed = true;
			String message = NLS.bind(Messages.history_errorContentDescription, getFullPath());		
			throw new ResourceException(IResourceStatus.FAILED_DESCRIBING_CONTENTS, getFullPath(), message, e);
		} finally {
			try {
				contents.close();
			} catch (IOException e) {
				if (!failed) {
					String message = NLS.bind(Messages.history_errorContentDescription, getFullPath());		
					throw new ResourceException(IResourceStatus.FAILED_DESCRIBING_CONTENTS, getFullPath(), message, e);
				}
			}
		}
	}

	/* (non-Javadoc)
	 * @see IFileState#getContents()
	 */
	public InputStream getContents() throws CoreException {
		return store.getContents(this);
	}

	/* (non-Javadoc)
	 * @see IFileState#getFullPath()
	 */
	public IPath getFullPath() {
		return fullPath;
	}

	/* (non-Javadoc)
	 * @see IFileState#getModificationTime()
	 */
	public long getModificationTime() {
		return lastModified;
	}

	/* (non-Javadoc)
	 * @see IFileState#getName()
	 */
	public String getName() {
		return fullPath.lastSegment();
	}

	public UniversalUniqueIdentifier getUUID() {
		return uuid;
	}

	/* (non-Javadoc)
	 * @see IFileState#isReadOnly()
	 */
	public boolean isReadOnly() {
		return true;
	}

	/**
	 * Returns a string representation of this object. Used for debug only.
	 */
	public String toString() {
		StringBuffer s = new StringBuffer();
		s.append("FileState(uuid: "); //$NON-NLS-1$
		s.append(uuid.toString());
		s.append(", lastModified: "); //$NON-NLS-1$
		s.append(lastModified);
		s.append(", path: "); //$NON-NLS-1$
		s.append(fullPath);
		s.append(')');
		return s.toString();
	}
}
