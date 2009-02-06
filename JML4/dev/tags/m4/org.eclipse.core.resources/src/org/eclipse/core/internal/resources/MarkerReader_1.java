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
import java.util.*;
import org.eclipse.core.internal.utils.Messages;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceStatus;
import org.eclipse.core.runtime.*;

/**
 * This class is used to read markers from disk. This is for version 1. 
 */
public class MarkerReader_1 extends MarkerReader {

	// type constants
	public static final int INDEX = 1;
	public static final int QNAME = 2;

	// marker attribute types
	public static final int ATTRIBUTE_NULL = -1;
	public static final int ATTRIBUTE_BOOLEAN = 0;
	public static final int ATTRIBUTE_INTEGER = 1;
	public static final int ATTRIBUTE_STRING = 2;

	public MarkerReader_1(Workspace workspace) {
		super(workspace);
	}

	/**
	 * SAVE_FILE -> VERSION_ID RESOURCE+
	 * VERSION_ID -> 
	 * RESOURCE -> RESOURCE_PATH MARKERS_SIZE MARKER*
	 * RESOURCE_PATH -> String
	 * MARKERS_SIZE -> int
	 * MARKER -> MARKER_ID TYPE ATTRIBUTES_SIZE ATTRIBUTE*
	 * MARKER_ID -> long
	 * TYPE -> INDEX | QNAME
	 * INDEX -> int int
	 * QNAME -> int String
	 * ATTRIBUTES_SIZE -> int
	 * ATTRIBUTE -> ATTRIBUTE_KEY ATTRIBUTE_VALUE
	 * ATTRIBUTE_KEY -> String
	 * ATTRIBUTE_VALUE -> INTEGER_VALUE | BOOLEAN_VALUE | STRING_VALUE | NULL_VALUE
	 * INTEGER_VALUE -> int int
	 * BOOLEAN_VALUE -> int boolean
	 * STRING_VALUE -> int String
	 * NULL_VALUE -> int
	 */
	public void read(DataInputStream input, boolean generateDeltas) throws IOException, CoreException {
		try {
			List readTypes = new ArrayList(5);
			while (true) {
				IPath path = new Path(input.readUTF());
				int markersSize = input.readInt();
				MarkerSet markers = new MarkerSet(markersSize);
				for (int i = 0; i < markersSize; i++)
					markers.add(readMarkerInfo(input, readTypes));
				// if the resource doesn't exist then return. ensure we do this after
				// reading the markers from the file so we don't get into an
				// inconsistent state.
				ResourceInfo info = workspace.getResourceInfo(path, false, false);
				if (info == null)
					continue;
				info.setMarkers(markers);
				if (generateDeltas) {
					Resource resource = workspace.newResource(path, info.getType());
					// Iterate over all elements and add not null ones. This saves us from copying
					// and shrinking the array.
					IMarkerSetElement[] infos = markers.elements;
					ArrayList deltas = new ArrayList(infos.length);
					for (int i = 0; i < infos.length; i++)
						if (infos[i] != null)
							deltas.add(new MarkerDelta(IResourceDelta.ADDED, resource, (MarkerInfo) infos[i]));
					workspace.getMarkerManager().changedMarkers(resource, (IMarkerSetElement[]) deltas.toArray(new IMarkerSetElement[deltas.size()]));
				}
			}
		} catch (EOFException e) {
			// ignore end of file
		}
	}

	private Map readAttributes(DataInputStream input) throws IOException {
		int attributesSize = input.readInt();
		if (attributesSize == 0)
			return null;
		Map result = new MarkerAttributeMap(attributesSize);
		for (int j = 0; j < attributesSize; j++) {
			String key = input.readUTF();
			int type = input.readInt();
			Object value = null;
			switch (type) {
				case ATTRIBUTE_INTEGER :
					value = new Integer(input.readInt());
					break;
				case ATTRIBUTE_BOOLEAN :
					value = input.readBoolean() ? Boolean.TRUE : Boolean.FALSE;
					break;
				case ATTRIBUTE_STRING :
					value = input.readUTF();
					break;
				case ATTRIBUTE_NULL :
					// do nothing
					break;
			}
			if (value != null)
				result.put(key, value);
		}
		return result.isEmpty() ? null : result;
	}

	private MarkerInfo readMarkerInfo(DataInputStream input, List readTypes) throws IOException, CoreException {
		MarkerInfo info = new MarkerInfo();
		info.setId(input.readLong());
		int constant = input.readInt();
		switch (constant) {
			case QNAME :
				String type = input.readUTF();
				info.setType(type);
				readTypes.add(type);
				break;
			case INDEX :
				info.setType((String) readTypes.get(input.readInt()));
				break;
			default :
				//if we get here the marker file is corrupt
				String msg = Messages.resources_readMarkers;
				throw new ResourceException(IResourceStatus.FAILED_READ_METADATA, null, msg, null);
		}
		info.internalSetAttributes(readAttributes(input));
		return info;
	}
}
