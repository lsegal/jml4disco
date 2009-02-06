/*******************************************************************************
 * Copyright (c) 2005, 2007 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     IBM Corporation - initial API and implementation
 * Martin Oberhuber (Wind River) - [44107] Add symbolic links to ResourceAttributes API
 *******************************************************************************/
package org.eclipse.core.internal.utils;

import java.io.*;
import java.net.URI;
import org.eclipse.core.filesystem.*;
import org.eclipse.core.internal.resources.ResourceException;
import org.eclipse.core.internal.resources.Workspace;
import org.eclipse.core.resources.IResourceStatus;
import org.eclipse.core.resources.ResourceAttributes;
import org.eclipse.core.runtime.*;
import org.eclipse.osgi.util.NLS;

/**
 * Static utility methods for manipulating Files and URIs.
 */
public class FileUtil {
	/**
	 * Singleton buffer created to prevent buffer creations in the
	 * transferStreams method.  Used as an optimization, based on the assumption
	 * that multiple writes won't happen in a given instance of FileStore.
	 */
	private static final byte[] buffer = new byte[8192];

	/**
	 * Converts a ResourceAttributes object into an IFileInfo object.
	 * @param attributes The resource attributes
	 * @return The file info
	 */
	public static IFileInfo attributesToFileInfo(ResourceAttributes attributes) {
		IFileInfo fileInfo = EFS.createFileInfo();
		fileInfo.setAttribute(EFS.ATTRIBUTE_READ_ONLY, attributes.isReadOnly());
		fileInfo.setAttribute(EFS.ATTRIBUTE_EXECUTABLE, attributes.isExecutable());
		fileInfo.setAttribute(EFS.ATTRIBUTE_ARCHIVE, attributes.isArchive());
		fileInfo.setAttribute(EFS.ATTRIBUTE_HIDDEN, attributes.isHidden());
		return fileInfo;
	}

	/**
	 * Converts an IPath into its canonical form for the local file system.
	 */
	public static IPath canonicalPath(IPath path) {
		if (path == null)
			return null;
		try {
			final String pathString = path.toOSString();
			final String canonicalPath = new java.io.File(pathString).getCanonicalPath();
			//only create a new path if necessary
			if (canonicalPath.equals(pathString))
				return path;
			return new Path(canonicalPath);
		} catch (IOException e) {
			return path;
		}
	}

	/**
	 * Converts a URI into its canonical form.
	 */
	public static URI canonicalURI(URI uri) {
		if (uri == null)
			return null;
		if (EFS.SCHEME_FILE.equals(uri.getScheme())) {
			//only create a new URI if it is different
			final IPath inputPath = URIUtil.toPath(uri);
			final IPath canonicalPath = canonicalPath(inputPath);
			if (inputPath == canonicalPath)
				return uri;
			return URIUtil.toURI(canonicalPath);
		}
		return uri;
	}

	/**
	 * Returns true if the given file system locations overlap. If "bothDirections" is true,
	 * this means they are the same, or one is a proper prefix of the other.  If "bothDirections"
	 * is false, this method only returns true if the locations are the same, or the first location
	 * is a prefix of the second.  Returns false if the locations do not overlap
	 * Does the right thing with respect to case insensitive platforms.
	 */
	private static boolean computeOverlap(IPath location1, IPath location2, boolean bothDirections) {
		IPath one = location1;
		IPath two = location2;
		// If we are on a case-insensitive file system then convert to all lower case.
		if (!Workspace.caseSensitive) {
			one = new Path(location1.toOSString().toLowerCase());
			two = new Path(location2.toOSString().toLowerCase());
		}
		return one.isPrefixOf(two) || (bothDirections && two.isPrefixOf(one));
	}

	/**
	 * Returns true if the given file system locations overlap. If "bothDirections" is true,
	 * this means they are the same, or one is a proper prefix of the other.  If "bothDirections"
	 * is false, this method only returns true if the locations are the same, or the first location
	 * is a prefix of the second.  Returns false if the locations do not overlap
	 */
	private static boolean computeOverlap(URI location1, URI location2, boolean bothDirections) {
		if (location1.equals(location2))
			return true;
		String scheme1 = location1.getScheme();
		String scheme2 = location2.getScheme();
		if (scheme1 == null ? scheme2 != null : !scheme1.equals(scheme2))
			return false;
		if (EFS.SCHEME_FILE.equals(scheme1) && EFS.SCHEME_FILE.equals(scheme2))
			return computeOverlap(URIUtil.toPath(location1), URIUtil.toPath(location2), bothDirections);
		IFileSystem system = null;
		try {
			system = EFS.getFileSystem(scheme1);
		} catch (CoreException e) {
			//handled below
		}
		if (system == null) {
			//we are stuck with string comparison
			String string1 = location1.toString();
			String string2 = location2.toString();
			return string1.startsWith(string2) || (bothDirections && string2.startsWith(string1));
		}
		IFileStore store1 = system.getStore(location1);
		IFileStore store2 = system.getStore(location2);
		return store1.equals(store2) || store1.isParentOf(store2) || (bothDirections && store2.isParentOf(store1));
	}

	/**
	 * Converts an IFileInfo object into a ResourceAttributes object.
	 * @param fileInfo The file info
	 * @return The resource attributes
	 */
	public static ResourceAttributes fileInfoToAttributes(IFileInfo fileInfo) {
		ResourceAttributes attributes = new ResourceAttributes();
		attributes.setReadOnly(fileInfo.getAttribute(EFS.ATTRIBUTE_READ_ONLY));
		attributes.setArchive(fileInfo.getAttribute(EFS.ATTRIBUTE_ARCHIVE));
		attributes.setExecutable(fileInfo.getAttribute(EFS.ATTRIBUTE_EXECUTABLE));
		attributes.setHidden(fileInfo.getAttribute(EFS.ATTRIBUTE_HIDDEN));
		attributes.setSymbolicLink(fileInfo.getAttribute(EFS.ATTRIBUTE_SYMLINK));
		return attributes;
	}

	/**
	 * Returns true if the given file system locations overlap, and false otherwise. 
	 * Overlap means the locations are the same, or one is a proper prefix of the other.
	 */
	public static boolean isOverlapping(URI location1, URI location2) {
		return computeOverlap(location1, location2, true);
	}

	/**
	 * Returns true if location1 is the same as, or a proper prefix of, location2.
	 * Returns false otherwise.
	 */
	public static boolean isPrefixOf(IPath location1, IPath location2) {
		return computeOverlap(location1, location2, false);
	}

	/**
	 * Returns true if location1 is the same as, or a proper prefix of, location2.
	 * Returns false otherwise.
	 */
	public static boolean isPrefixOf(URI location1, URI location2) {
		return computeOverlap(location1, location2, false);
	}

	/**
	 * Closes a stream and ignores any resulting exception. This is useful
	 * when doing stream cleanup in a finally block where secondary exceptions
	 * are not worth logging.
	 */
	public static void safeClose(InputStream in) {
		try {
			if (in != null)
				in.close();
		} catch (IOException e) {
			//ignore
		}
	}

	/**
	 * Closes a stream and ignores any resulting exception. This is useful
	 * when doing stream cleanup in a finally block where secondary exceptions
	 * are not worth logging.
	 */
	public static void safeClose(OutputStream out) {
		try {
			if (out != null)
				out.close();
		} catch (IOException e) {
			//ignore
		}
	}

	/**
	 * Converts a URI to an IPath.  Returns null if the URI cannot be represented
	 * as an IPath.
	 * <p>
	 * Note this method differs from URIUtil in its handling of relative URIs
	 * as being relative to path variables.
	 */
	public static IPath toPath(URI uri) {
		if (uri == null)
			return null;
		final String scheme = uri.getScheme();
		// null scheme represents path variable
		if (scheme == null || EFS.SCHEME_FILE.equals(scheme))
			return new Path(uri.getSchemeSpecificPart());
		return null;
	}

	public static final void transferStreams(InputStream source, OutputStream destination, String path, IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		try {
			/*
			 * Note: although synchronizing on the buffer is thread-safe,
			 * it may result in slower performance in the future if we want 
			 * to allow concurrent writes.
			 */
			synchronized (buffer) {
				while (true) {
					int bytesRead = -1;
					try {
						bytesRead = source.read(buffer);
					} catch (IOException e) {
						String msg = NLS.bind(Messages.localstore_failedReadDuringWrite, path);
						throw new ResourceException(IResourceStatus.FAILED_READ_LOCAL, new Path(path), msg, e);
					}
					if (bytesRead == -1)
						break;
					try {
						destination.write(buffer, 0, bytesRead);
					} catch (IOException e) {
						String msg = NLS.bind(Messages.localstore_couldNotWrite, path);
						throw new ResourceException(IResourceStatus.FAILED_WRITE_LOCAL, new Path(path), msg, e);
					}
					monitor.worked(1);
				}
			}
		} finally {
			safeClose(source);
			safeClose(destination);
		}
	}

	/**
	 * Not intended for instantiation.
	 */
	private FileUtil() {
		super();
	}
}