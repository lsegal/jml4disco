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
package org.eclipse.core.internal.resources;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import org.eclipse.core.internal.utils.Messages;
import org.eclipse.core.internal.utils.ObjectMap;
import org.eclipse.core.resources.IResourceStatus;
import org.eclipse.core.runtime.*;
import org.eclipse.osgi.util.NLS;

/**
 * This class is used to read sync info from disk. This is the implementation
 * for reading files with version number 2.
 */
public class SyncInfoReader_2 extends SyncInfoReader {

	// for sync info
	public static final int INDEX = 1;
	public static final int QNAME = 2;

	public SyncInfoReader_2(Workspace workspace, Synchronizer synchronizer) {
		super(workspace, synchronizer);
	}

	/**
	 * SAVE_FILE -> VERSION_ID RESOURCE*
	 * VERSION_ID -> int
	 * RESOURCE -> RESOURCE_PATH SIZE SYNCINFO*
	 * RESOURCE_PATH -> String
	 * SIZE -> int
	 * SYNCINFO -> TYPE BYTES
	 * TYPE -> INDEX | QNAME
	 * INDEX -> int int
	 * QNAME -> int String
	 * BYTES -> byte[]
	 * 
	 */
	public void readSyncInfo(DataInputStream input) throws IOException, CoreException {
		try {
			List readPartners = new ArrayList(5);
			while (true) {
				IPath path = new Path(input.readUTF());
				readSyncInfo(path, input, readPartners);
			}
		} catch (EOFException e) {
			// ignore end of file
		}
	}

	private void readSyncInfo(IPath path, DataInputStream input, List readPartners) throws IOException, CoreException {
		int size = input.readInt();
		ObjectMap table = new ObjectMap(size);
		for (int i = 0; i < size; i++) {
			QualifiedName name = null;
			int type = input.readInt();
			switch (type) {
				case QNAME :
					String qualifier = input.readUTF();
					String local = input.readUTF();
					name = new QualifiedName(qualifier, local);
					readPartners.add(name);
					break;
				case INDEX :
					name = (QualifiedName) readPartners.get(input.readInt());
					break;
				default :
					//if we get here then the sync info file is corrupt
					String msg = NLS.bind(Messages.resources_readSync, path == null ? "" : path.toString()); //$NON-NLS-1$
					throw new ResourceException(IResourceStatus.FAILED_READ_METADATA, path, msg, null);
			}
			// read the bytes
			int length = input.readInt();
			byte[] bytes = new byte[length];
			input.readFully(bytes);
			// put them in the table
			table.put(name, bytes);
		}
		// set the table on the resource info
		ResourceInfo info = workspace.getResourceInfo(path, true, false);
		if (info == null)
			return;
		info.setSyncInfo(table);
		info.clear(ICoreConstants.M_SYNCINFO_SNAP_DIRTY);
	}
}
