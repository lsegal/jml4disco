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

import java.util.Iterator;
import java.util.Map;
import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.IPath;

/**
 * @see IMarkerDelta
 */
public class MarkerDelta implements IMarkerDelta, IMarkerSetElement {
	protected int kind;
	protected IResource resource;
	protected MarkerInfo info;

	/**
	 * Creates a new marker delta.
	 */
	public MarkerDelta(int kind, IResource resource, MarkerInfo info) {
		this.kind = kind;
		this.resource = resource;
		this.info = info;
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getAttribute(String)
	 */
	public Object getAttribute(String attributeName) {
		return info.getAttribute(attributeName);
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getAttribute(String, int)
	 */
	public int getAttribute(String attributeName, int defaultValue) {
		Object value = info.getAttribute(attributeName);
		if (value instanceof Integer)
			return ((Integer) value).intValue();
		return defaultValue;
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getAttribute(String, String)
	 */
	public String getAttribute(String attributeName, String defaultValue) {
		Object value = info.getAttribute(attributeName);
		if (value instanceof String)
			return (String) value;
		return defaultValue;
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getAttribute(String, boolean)
	 */
	public boolean getAttribute(String attributeName, boolean defaultValue) {
		Object value = info.getAttribute(attributeName);
		if (value instanceof Boolean)
			return ((Boolean) value).booleanValue();
		return defaultValue;
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getAttributes()
	 */
	public Map getAttributes() {
		return info.getAttributes();
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getAttributes(String[])
	 */
	public Object[] getAttributes(String[] attributeNames) {
		return info.getAttributes(attributeNames);
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getId()
	 */
	public long getId() {
		return info.getId();
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getKind()
	 */
	public int getKind() {
		return kind;
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getMarker()
	 */
	public IMarker getMarker() {
		return new Marker(resource, getId());
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getResource()
	 */
	public IResource getResource() {
		return resource;
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#getType()
	 */
	public String getType() {
		return info.getType();
	}

	/* (non-Javadoc)
	 * @see IMarkerDelta#isSubtypeOf(String)
	 */
	public boolean isSubtypeOf(String superType) {
		return ((Workspace) getResource().getWorkspace()).getMarkerManager().isSubtype(getType(), superType);
	}

	/**
	 * Merge two Maps of (IPath->MarkerSet) representing changes.  Use the old
	 * map to store the result so we don't have to build a new map to return.
	 */
	public static Map merge(Map oldChanges, Map newChanges) {
		if (oldChanges == null)
			//don't worry about copying since the new changes are no longer used
			return newChanges;
		if (newChanges == null)
			return oldChanges;
		for (Iterator it = newChanges.keySet().iterator(); it.hasNext();) {
			IPath key = (IPath) it.next();
			MarkerSet oldSet = (MarkerSet) oldChanges.get(key);
			MarkerSet newSet = (MarkerSet) newChanges.get(key);
			if (oldSet == null)
				oldChanges.put(key, newSet);
			else
				merge(oldSet, newSet.elements());
		}
		return oldChanges;
	}

	/**
	 * Merge two sets of marker changes.  Both sets must be on the same resource. Use the original set
	 * of changes to store the result so we don't have to build a completely different set to return.
	 * 
	 * add + add = N/A
	 * add + remove = nothing (no delta)
	 * add + change = add
	 * remove + add = N/A
	 * remove + remove = N/A
	 * remove + change = N/A
	 * change + add = N/A
	 * change + change = change  (note: info held onto by the marker delta should be that of the oldest change, and not replaced when composed)
	 * change + remove = remove (note: info held onto by the marker delta should be that of the oldest change, and not replaced when changed to a remove)
	 */
	protected static MarkerSet merge(MarkerSet oldChanges, IMarkerSetElement[] newChanges) {
		if (oldChanges == null) {
			MarkerSet result = new MarkerSet(newChanges.length);
			for (int i = 0; i < newChanges.length; i++)
				result.add(newChanges[i]);
			return result;
		}
		if (newChanges == null)
			return oldChanges;

		for (int i = 0; i < newChanges.length; i++) {
			MarkerDelta newDelta = (MarkerDelta) newChanges[i];
			MarkerDelta oldDelta = (MarkerDelta) oldChanges.get(newDelta.getId());
			if (oldDelta == null) {
				oldChanges.add(newDelta);
				continue;
			}
			switch (oldDelta.getKind()) {
				case IResourceDelta.ADDED :
					switch (newDelta.getKind()) {
						case IResourceDelta.ADDED :
							// add + add = N/A
							break;
						case IResourceDelta.REMOVED :
							// add + remove = nothing
							// Remove the original ADD delta.
							oldChanges.remove(oldDelta);
							break;
						case IResourceDelta.CHANGED :
							// add + change = add
							break;
					}
					break;
				case IResourceDelta.REMOVED :
					switch (newDelta.getKind()) {
						case IResourceDelta.ADDED :
							// remove + add = N/A
							break;
						case IResourceDelta.REMOVED :
							// remove + remove = N/A
							break;
						case IResourceDelta.CHANGED :
							// remove + change = N/A
							break;
					}
					break;
				case IResourceDelta.CHANGED :
					switch (newDelta.getKind()) {
						case IResourceDelta.ADDED :
							// change + add = N/A
							break;
						case IResourceDelta.REMOVED :
							// change + remove = remove
							// Change the delta kind.
							oldDelta.setKind(IResourceDelta.REMOVED);
							break;
						case IResourceDelta.CHANGED :
							// change + change = change
							break;
					}
					break;
			}
		}
		return oldChanges;
	}

	private void setKind(int kind) {
		this.kind = kind;
	}
}
