/*******************************************************************************
 * Copyright (c) 2004, 2008 Red Hat Incorporated and others
 * All rights reserved. This program and the accompanying materials 
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/org/documents/epl-v10.html
 * 
 * Contributors:
 *     IBM Corporation - initial API 
 *     Red Hat Incorporated - initial implementation
 * 	Martin Oberhuber (Wind River) - [44107] Add symbolic links to ResourceAttributes API
 *******************************************************************************/

package org.eclipse.core.resources;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.internal.utils.FileUtil;
import org.eclipse.core.runtime.CoreException;

/**
 * This class represents platform specific attributes of files.
 * Any attributes can be added, but only the attributes that are 
 * supported by the platform will be used. These methods do not set the 
 * attributes in the file system.
 * 
 * @author Red Hat Incorporated
 * @see IResource#getResourceAttributes()
 * @see IResource#setResourceAttributes(ResourceAttributes)
 * @since 3.1
 * @noextend This class is not intended to be subclassed by clients.
 */
public class ResourceAttributes {
	private int attributes;

	/**
	 * Creates a new resource attributes instance with attributes
	 * taken from the specified file in the file system.  If the specified
	 * file does not exist or is not accessible, this method has the
	 * same effect as calling the default constructor.
	 * 
	 * @param file The file to get attributes from
	 * @return A resource attributes object
	 */
	public static ResourceAttributes fromFile(java.io.File file) {
		try {
			return FileUtil.fileInfoToAttributes(EFS.getStore(file.toURI()).fetchInfo());
		} catch (CoreException e) {
			//file could not be accessed
			return new ResourceAttributes();
		}
	}

	/**
	 * Creates a new instance of <code>ResourceAttributes</code>.
	 */
	public ResourceAttributes() {
		super();
	}

	/**
	 * Returns whether this ResourceAttributes object is marked archive.
	 *
	 * @return <code>true</code> if this resource is marked archive, 
	 *		<code>false</code> otherwise
	 * @see #setArchive(boolean)
	 */
	public boolean isArchive() {
		return (attributes & EFS.ATTRIBUTE_ARCHIVE) != 0;
	}

	/**
	 * Returns whether this ResourceAttributes object is marked executable.
	 *
	 * @return <code>true</code> if this resource is marked executable, 
	 *		<code>false</code> otherwise
	 * @see #setExecutable(boolean)
	 */
	public boolean isExecutable() {
		return (attributes & EFS.ATTRIBUTE_EXECUTABLE) != 0;
	}

	/**
	 * Returns whether this ResourceAttributes object is marked hidden.
	 *
	 * @return <code>true</code> if this resource is marked hidden, 
	 *		<code>false</code> otherwise
	 * @see #setHidden(boolean)
	 * @since 3.2
	 */
	public boolean isHidden() {
		return (attributes & EFS.ATTRIBUTE_HIDDEN) != 0;
	}

	/**
	 * Returns whether this ResourceAttributes object is marked read only.
	 *
	 * @return <code>true</code> if this resource is marked as read only, 
	 *		<code>false</code> otherwise
	 * @see #setReadOnly(boolean)
	 */
	public boolean isReadOnly() {
		return (attributes & EFS.ATTRIBUTE_READ_ONLY) != 0;
	}

	/**
	 * Returns whether this ResourceAttributes object is marked read only.
	 *
	 * @return <code>true</code> if this resource is marked as symbolic link, 
	 *		<code>false</code> otherwise
	 * @see #setSymbolicLink(boolean)
	 * @since 3.4
	 */
	public boolean isSymbolicLink() {
		return (attributes & EFS.ATTRIBUTE_SYMLINK) != 0;
	}

	/**
	 * Sets or unsets whether this ResourceAttributes object is marked archive.
	 *
	 * @param archive <code>true</code> to set it to be archive, 
	 *		<code>false</code> to unset
	 * @see #isArchive()
	 */
	public void setArchive(boolean archive) {
		set(EFS.ATTRIBUTE_ARCHIVE, archive);
	}

	/** 
	 * Clears all of the bits indicated by the mask.
	 */
	private void set(int mask, boolean value) {
		if (value)
			attributes |= mask;
		else
			attributes &= ~mask;
	}

	/**
	 * Sets or unsets whether this ResourceAttributes object is marked executable.
	 *
	 * @param executable <code>true</code> to set it to be executable, 
	 *		<code>false</code> to unset
	 * @see #isExecutable()
	 */
	public void setExecutable(boolean executable) {
		set(EFS.ATTRIBUTE_EXECUTABLE, executable);
	}

	/**
	 * Sets or unsets whether this ResourceAttributes object is marked hidden
	 *
	 * @param hidden <code>true</code> to set it to be marked hidden,
	 *		<code>false</code> to unset
	 * @see #isHidden()
	 * @since 3.2
	 */
	public void setHidden(boolean hidden) {
		set(EFS.ATTRIBUTE_HIDDEN, hidden);
	}

	/**
	 * Sets or unsets whether this ResourceAttributes object is marked read only.
	 *
	 * @param readOnly <code>true</code> to set it to be marked read only, 
	 *		<code>false</code> to unset
	 * @see #isReadOnly()
	 */
	public void setReadOnly(boolean readOnly) {
		set(EFS.ATTRIBUTE_READ_ONLY, readOnly);
	}

	/**
	 * Sets or unsets whether this ResourceAttributes object is marked as symbolic link.
	 *
	 * @param symLink <code>true</code> to set it to be marked as symbolic link, 
	 *		<code>false</code> to unset
	 * @see #isSymbolicLink()
	 * @since 3.4
	 */
	public void setSymbolicLink(boolean symLink) {
		set(EFS.ATTRIBUTE_SYMLINK, symLink);
	}

	/**
	 * Returns a string representation of the attributes, suitable 
	 * for debugging purposes only.
	 */
	public String toString() {
		return "ResourceAttributes(" + attributes + ')'; //$NON-NLS-1$
	}
}