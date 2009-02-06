/*******************************************************************************
 * Copyright (c) 2000, 2005 IBM Corporation and others.
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

/**
 * Appends data, in chunks, to a file. Each chunk is defined by the moment
 * the stream is opened (created) and a call to #succeed is made. It is
 * necessary to use the <code>SafeChunkyInputStream</code> to read its
 * contents back. The user of this class does not need to know explicitly about
 * its chunk implementation.
 * It is only an implementation detail. What really matters to the outside
 * world is that it tries to keep the file data consistent.
 * If some data becomes corrupted while writing or later, upon reading
 * the file, the chunk that contains the corrupted data is skipped.
 * <p>
 * Because of this class purpose (keep data consistent), it is important that the
 * user only calls <code>#succeed</code> when the chunk of data is successfully
 * written. After this call, the user can continue writing data to the file and it
 * will not be considered related to the previous chunk. So, if this data is
 * corrupted, the previous one is still safe.
 *
 * @see SafeChunkyInputStream
 */
public class SafeChunkyOutputStream extends FilterOutputStream {
	protected String filePath;
	protected boolean isOpen;

	public SafeChunkyOutputStream(File target) throws IOException {
		this(target.getAbsolutePath());
	}

	public SafeChunkyOutputStream(String filePath) throws IOException {
		super(new BufferedOutputStream(new FileOutputStream(filePath, true)));
		this.filePath = filePath;
		isOpen = true;
		beginChunk();
	}

	protected void beginChunk() throws IOException {
		write(ILocalStoreConstants.BEGIN_CHUNK);
	}

	protected void endChunk() throws IOException {
		write(ILocalStoreConstants.END_CHUNK);
	}

	protected void open() throws IOException {
		out = new BufferedOutputStream(new FileOutputStream(filePath, true));
		isOpen = true;
		beginChunk();
	}

	public void succeed() throws IOException {
		try {
			endChunk();
		} finally {
			isOpen = false;
			close();
		}
	}

	public void write(int b) throws IOException {
		if (!isOpen)
			open();
		super.write(b);
	}
}
