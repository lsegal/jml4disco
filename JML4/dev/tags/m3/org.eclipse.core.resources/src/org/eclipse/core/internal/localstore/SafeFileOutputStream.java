/*******************************************************************************
 * Copyright (c) 2000, 2006 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.core.internal.localstore;

import java.io.*;
import org.eclipse.core.internal.utils.FileUtil;

/**
 * This class should be used when there's a file already in the
 * destination and we don't want to lose its contents if a
 * failure writing this stream happens.
 * Basically, the new contents are written to a temporary location.
 * If everything goes OK, it is moved to the right place.
 * The user has the option to define the temporary location or 
 * it will be created in the default-temporary directory
 * (see java.io.File for details).
 */
public class SafeFileOutputStream extends OutputStream {
	protected File temp;
	protected File target;
	protected OutputStream output;
	protected boolean failed;
	protected static final String EXTENSION = ".bak"; //$NON-NLS-1$

	public SafeFileOutputStream(File file) throws IOException {
		this(file.getAbsolutePath(), null);
	}

	/**
	 * If targetPath is null, the file will be created in the default-temporary directory.
	 */
	public SafeFileOutputStream(String targetPath, String tempPath) throws IOException {
		failed = false;
		target = new File(targetPath);
		createTempFile(tempPath);
		if (!target.exists()) {
			if (!temp.exists()) {
				output = new BufferedOutputStream(new FileOutputStream(target));
				return;
			}
			// If we do not have a file at target location, but we do have at temp location,
			// it probably means something wrong happened the last time we tried to write it.
			// So, try to recover the backup file. And, if successful, write the new one.
			copy(temp, target);
		}
		output = new BufferedOutputStream(new FileOutputStream(temp));
	}

	public void close() throws IOException {
		try {
			output.close();
		} catch (IOException e) {
			failed = true;
			throw e; // rethrow
		}
		if (failed)
			temp.delete();
		else
			commit();
	}

	protected void commit() throws IOException {
		if (!temp.exists())
			return;
		target.delete();
		copy(temp, target);
		temp.delete();
	}

	protected void copy(File sourceFile, File destinationFile) throws IOException {
		if (!sourceFile.exists())
			return;
		if (sourceFile.renameTo(destinationFile))
			return;
		InputStream source = null;
		OutputStream destination = null;
		try {
			source = new BufferedInputStream(new FileInputStream(sourceFile));
			destination = new BufferedOutputStream(new FileOutputStream(destinationFile));
			transferStreams(source, destination);
		} finally {
			FileUtil.safeClose(source);
			FileUtil.safeClose(destination);
		}
	}

	protected void createTempFile(String tempPath) {
		if (tempPath == null)
			tempPath = target.getAbsolutePath() + EXTENSION;
		temp = new File(tempPath);
	}

	public void flush() throws IOException {
		try {
			output.flush();
		} catch (IOException e) {
			failed = true;
			throw e; // rethrow
		}
	}

	public String getTempFilePath() {
		return temp.getAbsolutePath();
	}

	protected void transferStreams(InputStream source, OutputStream destination) throws IOException {
		byte[] buffer = new byte[8192];
		while (true) {
			int bytesRead = source.read(buffer);
			if (bytesRead == -1)
				break;
			destination.write(buffer, 0, bytesRead);
		}
	}

	public void write(int b) throws IOException {
		try {
			output.write(b);
		} catch (IOException e) {
			failed = true;
			throw e; // rethrow
		}
	}
}
