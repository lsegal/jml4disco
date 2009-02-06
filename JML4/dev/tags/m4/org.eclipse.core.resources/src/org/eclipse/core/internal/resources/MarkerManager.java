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
import java.util.*;
import org.eclipse.core.internal.localstore.SafeChunkyInputStream;
import org.eclipse.core.internal.localstore.SafeFileInputStream;
import org.eclipse.core.internal.utils.Messages;
import org.eclipse.core.internal.utils.Policy;
import org.eclipse.core.internal.watson.*;
import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.*;
import org.eclipse.osgi.util.NLS;

/**
 * A marker manager stores and retrieves markers on resources in the workspace.
 */
public class MarkerManager implements IManager {

	//singletons
	private static final MarkerInfo[] NO_MARKER_INFO = new MarkerInfo[0];
	private static final IMarker[] NO_MARKERS = new IMarker[0];
	protected MarkerTypeDefinitionCache cache = new MarkerTypeDefinitionCache();
	private long changeId = 0;
	protected Map currentDeltas = null;
	protected final MarkerDeltaManager deltaManager = new MarkerDeltaManager();

	protected Workspace workspace;
	protected MarkerWriter writer = new MarkerWriter(this);

	/**
	 * Creates a new marker manager
	 */
	public MarkerManager(Workspace workspace) {
		this.workspace = workspace;
	}

	/* (non-Javadoc)
	 * Adds the given markers to the given resource.
	 * 
	 * @see IResource#createMarker(String) 
	 */
	public void add(IResource resource, MarkerInfo newMarker) throws CoreException {
		Resource target = (Resource) resource;
		ResourceInfo info = workspace.getResourceInfo(target.getFullPath(), false, false);
		target.checkExists(target.getFlags(info), false);
		info = workspace.getResourceInfo(resource.getFullPath(), false, true);
		//resource may have been deleted concurrently -- just bail out if this happens
		if (info == null)
			return;
		// set the M_MARKERS_SNAP_DIRTY flag to indicate that this
		// resource's markers have changed since the last snapshot
		if (isPersistent(newMarker))
			info.set(ICoreConstants.M_MARKERS_SNAP_DIRTY);
		//Concurrency: copy the marker set on modify
		MarkerSet markers = info.getMarkers(true);
		if (markers == null)
			markers = new MarkerSet(1);
		basicAdd(resource, markers, newMarker);
		if (!markers.isEmpty())
			info.setMarkers(markers);
	}

	/**
	 * Adds the new markers to the given set of markers.  If added, the markers
	 * are associated with the specified resource.IMarkerDeltas for Added markers 
	 * are generated.
	 */
	private void basicAdd(IResource resource, MarkerSet markers, MarkerInfo newMarker) throws CoreException {
		// should always be a new marker.
		if (newMarker.getId() != MarkerInfo.UNDEFINED_ID) {
			String message = Messages.resources_changeInAdd;
			throw new ResourceException(new ResourceStatus(IResourceStatus.INTERNAL_ERROR, resource.getFullPath(), message));
		}
		newMarker.setId(workspace.nextMarkerId());
		markers.add(newMarker);
		IMarkerSetElement[] changes = new IMarkerSetElement[1];
		changes[0] = new MarkerDelta(IResourceDelta.ADDED, resource, newMarker);
		changedMarkers(resource, changes);
	}

	/**
	 * Returns the markers in the given set of markers which match the given type.
	 */
	protected MarkerInfo[] basicFindMatching(MarkerSet markers, String type, boolean includeSubtypes) {
		int size = markers.size();
		if (size <= 0)
			return NO_MARKER_INFO;
		List result = new ArrayList(size);
		IMarkerSetElement[] elements = markers.elements();
		for (int i = 0; i < elements.length; i++) {
			MarkerInfo marker = (MarkerInfo) elements[i];
			// if the type is null then we are looking for all types of markers
			if (type == null)
				result.add(marker);
			else {
				if (includeSubtypes) {
					if (cache.isSubtype(marker.getType(), type))
						result.add(marker);
				} else {
					if (marker.getType().equals(type))
						result.add(marker);
				}
			}
		}
		size = result.size();
		if (size <= 0)
			return NO_MARKER_INFO;
		return (MarkerInfo[]) result.toArray(new MarkerInfo[size]);
	}

	protected int basicFindMaxSeverity(MarkerSet markers, String type, boolean includeSubtypes) {
		int max = -1;
		int size = markers.size();
		if (size <= 0)
			return max;
		IMarkerSetElement[] elements = markers.elements();
		for (int i = 0; i < elements.length; i++) {
			MarkerInfo marker = (MarkerInfo) elements[i];
			// if the type is null then we are looking for all types of markers
			if (type == null)
				max = Math.max(max, getSeverity(marker));
			else {
				if (includeSubtypes) {
					if (cache.isSubtype(marker.getType(), type))
						max = Math.max(max, getSeverity(marker));
				} else {
					if (marker.getType().equals(type))
						max = Math.max(max, getSeverity(marker));
				}
			}
			if (max >= IMarker.SEVERITY_ERROR) {
				break;
			}
		}
		return max;
	}

	private int getSeverity(MarkerInfo marker) {
		Object o = marker.getAttribute(IMarker.SEVERITY);
		if (o instanceof Integer) {
			Integer i = (Integer) o;
			return i.intValue();
		}
		return -1;
	}

	/**
	 * Removes markers of the specified type from the given resource.
	 * Note: this method is protected to avoid creation of a synthetic accessor (it
	 * is called from an anonymous inner class).
	 */
	protected void basicRemoveMarkers(ResourceInfo info, IPathRequestor requestor, String type, boolean includeSubtypes) {
		MarkerSet markers = info.getMarkers(false);
		if (markers == null)
			return;
		IMarkerSetElement[] matching;
		IPath path;
		if (type == null) {
			// if the type is null, all markers are to be removed.
			//now we need to crack open the tree
			path = requestor.requestPath();
			info = workspace.getResourceInfo(path, false, true);
			info.setMarkers(null);
			matching = markers.elements();
		} else {
			matching = basicFindMatching(markers, type, includeSubtypes);
			// if none match, there is nothing to remove
			if (matching.length == 0)
				return;
			//now we need to crack open the tree
			path = requestor.requestPath();
			info = workspace.getResourceInfo(path, false, true);
			//Concurrency: copy the marker set on modify
			markers = info.getMarkers(true);
			// remove all the matching markers and also the whole 
			// set if there are no remaining markers
			markers.removeAll(matching);
			info.setMarkers(markers.size() == 0 ? null : markers);
		}
		info.set(ICoreConstants.M_MARKERS_SNAP_DIRTY);
		IMarkerSetElement[] changes = new IMarkerSetElement[matching.length];
		IResource resource = workspace.getRoot().findMember(path);
		for (int i = 0; i < matching.length; i++)
			changes[i] = new MarkerDelta(IResourceDelta.REMOVED, resource, (MarkerInfo) matching[i]);
		changedMarkers(resource, changes);
		return;
	}

	/**
	 * Adds the markers on the given target which match the specified type to the list.
	 */
	protected void buildMarkers(IMarkerSetElement[] markers, IPath path, int type, ArrayList list) {
		if (markers.length == 0)
			return;
		IResource resource = workspace.newResource(path, type);
		list.ensureCapacity(list.size() + markers.length);
		for (int i = 0; i < markers.length; i++) {
			list.add(new Marker(resource, ((MarkerInfo) markers[i]).getId()));
		}
	}

	/**
	 * Markers have changed on the given resource.  Remember the changes for subsequent notification.
	 */
	protected void changedMarkers(IResource resource, IMarkerSetElement[] changes) {
		if (changes == null || changes.length == 0)
			return;
		changeId++;
		if (currentDeltas == null)
			currentDeltas = deltaManager.newGeneration(changeId);
		IPath path = resource.getFullPath();
		MarkerSet previousChanges = (MarkerSet) currentDeltas.get(path);
		MarkerSet result = MarkerDelta.merge(previousChanges, changes);
		if (result.size() == 0)
			currentDeltas.remove(path);
		else
			currentDeltas.put(path, result);
		ResourceInfo info = workspace.getResourceInfo(path, false, true);
		if (info != null)
			info.incrementMarkerGenerationCount();
	}

	/**
	 * Returns the marker with the given id or <code>null</code> if none is found.
	 */
	public IMarker findMarker(IResource resource, long id) {
		MarkerInfo info = findMarkerInfo(resource, id);
		return info == null ? null : new Marker(resource, info.getId());
	}

	/**
	 * Returns the marker with the given id or <code>null</code> if none is found.
	 */
	public MarkerInfo findMarkerInfo(IResource resource, long id) {
		ResourceInfo info = workspace.getResourceInfo(resource.getFullPath(), false, false);
		if (info == null)
			return null;
		MarkerSet markers = info.getMarkers(false);
		if (markers == null)
			return null;
		return (MarkerInfo) markers.get(id);
	}

	/**
	 * Returns all markers of the specified type on the given target, with option
	 * to search the target's children.
	 * Passing <code>null</code> for the type specifies a match
	 * for all types (i.e., <code>null</code> is a wildcard.
	 */
	public IMarker[] findMarkers(IResource target, final String type, final boolean includeSubtypes, int depth) {
		ArrayList result = new ArrayList();
		doFindMarkers(target, result, type, includeSubtypes, depth);
		if (result.size() == 0)
			return NO_MARKERS;
		return (IMarker[]) result.toArray(new IMarker[result.size()]);
	}

	/**
	 * Fills the provided list with all markers of the specified type on the given target, 
	 * with option to search the target's children.
	 * Passing <code>null</code> for the type specifies a match
	 * for all types (i.e., <code>null</code> is a wildcard.
	 */
	public void doFindMarkers(IResource target, ArrayList result, final String type, final boolean includeSubtypes, int depth) {
		//optimize the deep searches with an element tree visitor
		if (depth == IResource.DEPTH_INFINITE && target.getType() != IResource.FILE)
			visitorFindMarkers(target.getFullPath(), result, type, includeSubtypes);
		else
			recursiveFindMarkers(target.getFullPath(), result, type, includeSubtypes, depth);
	}

	/**
	 * Finds the max severity across all problem markers on the given target, 
	 * with option to search the target's children.
	 */
	public int findMaxProblemSeverity(IResource target, String type, boolean includeSubtypes, int depth) {
		//optimize the deep searches with an element tree visitor
		if (depth == IResource.DEPTH_INFINITE && target.getType() != IResource.FILE)
			return visitorFindMaxSeverity(target.getFullPath(), type, includeSubtypes);
		return recursiveFindMaxSeverity(target.getFullPath(), type, includeSubtypes, depth);
	}

	public long getChangeId() {
		return changeId;
	}

	/**
	 * Returns the map of all marker deltas since the given change Id.
	 */
	public Map getMarkerDeltas(long startChangeId) {
		return deltaManager.assembleDeltas(startChangeId);
	}

	/**
	 * Returns true if this manager has a marker delta record
	 * for the given marker id, and false otherwise.
	 */
	boolean hasDelta(IPath path, long id) {
		if (currentDeltas == null)
			return false;
		MarkerSet set = (MarkerSet) currentDeltas.get(path);
		if (set == null)
			return false;
		return set.get(id) != null;
	}

	/**
	 * Returns true if the given marker is persistent, and false
	 * otherwise.
	 */
	public boolean isPersistent(MarkerInfo info) {
		if (!cache.isPersistent(info.getType()))
			return false;
		Object isTransient = info.getAttribute(IMarker.TRANSIENT);
		return isTransient == null || !(isTransient instanceof Boolean) || !((Boolean) isTransient).booleanValue();
	}

	/**
	 * Returns true if <code>type</code> is a sub type of <code>superType</code>.
	 */
	public boolean isSubtype(String type, String superType) {
		return cache.isSubtype(type, superType);
	}

	public void moved(final IResource source, final IResource destination, int depth) throws CoreException {
		final int count = destination.getFullPath().segmentCount();

		// we removed from the source and added to the destination
		IResourceVisitor visitor = new IResourceVisitor() {
			public boolean visit(IResource resource) {
				Resource r = (Resource) resource;
				ResourceInfo info = r.getResourceInfo(false, true);
				MarkerSet markers = info.getMarkers(false);
				if (markers == null)
					return true;
				info.set(ICoreConstants.M_MARKERS_SNAP_DIRTY);
				IMarkerSetElement[] removed = new IMarkerSetElement[markers.size()];
				IMarkerSetElement[] added = new IMarkerSetElement[markers.size()];
				IPath path = resource.getFullPath().removeFirstSegments(count);
				path = source.getFullPath().append(path);
				IResource sourceChild = workspace.newResource(path, resource.getType());
				IMarkerSetElement[] elements = markers.elements();
				for (int i = 0; i < elements.length; i++) {
					// calculate the ADDED delta
					MarkerInfo markerInfo = (MarkerInfo) elements[i];
					MarkerDelta delta = new MarkerDelta(IResourceDelta.ADDED, resource, markerInfo);
					added[i] = delta;
					// calculate the REMOVED delta
					delta = new MarkerDelta(IResourceDelta.REMOVED, sourceChild, markerInfo);
					removed[i] = delta;
				}
				changedMarkers(resource, added);
				changedMarkers(sourceChild, removed);
				return true;
			}
		};
		destination.accept(visitor, depth, IContainer.INCLUDE_TEAM_PRIVATE_MEMBERS | IContainer.INCLUDE_HIDDEN);
	}

	/**
	 * Adds the markers for a subtree of resources to the list.
	 */
	private void recursiveFindMarkers(IPath path, ArrayList list, String type, boolean includeSubtypes, int depth) {
		ResourceInfo info = workspace.getResourceInfo(path, false, false);
		if (info == null)
			return;
		MarkerSet markers = info.getMarkers(false);

		//add the matching markers for this resource
		if (markers != null) {
			IMarkerSetElement[] matching;
			if (type == null)
				matching = markers.elements();
			else
				matching = basicFindMatching(markers, type, includeSubtypes);
			buildMarkers(matching, path, info.getType(), list);
		}

		//recurse
		if (depth == IResource.DEPTH_ZERO || info.getType() == IResource.FILE)
			return;
		if (depth == IResource.DEPTH_ONE)
			depth = IResource.DEPTH_ZERO;
		IPath[] children = workspace.getElementTree().getChildren(path);
		for (int i = 0; i < children.length; i++) {
			recursiveFindMarkers(children[i], list, type, includeSubtypes, depth);
		}
	}

	/**
	 * Finds the max severity across problem markers for a subtree of resources.
	 */
	private int recursiveFindMaxSeverity(IPath path, String type, boolean includeSubtypes, int depth) {
		ResourceInfo info = workspace.getResourceInfo(path, false, false);
		if (info == null)
			return -1;
		MarkerSet markers = info.getMarkers(false);

		//add the matching markers for this resource
		int max = -1;
		if (markers != null) {
			max = basicFindMaxSeverity(markers, type, includeSubtypes);
			if (max >= IMarker.SEVERITY_ERROR) {
				return max;
			}
		}

		//recurse
		if (depth == IResource.DEPTH_ZERO || info.getType() == IResource.FILE)
			return max;
		if (depth == IResource.DEPTH_ONE)
			depth = IResource.DEPTH_ZERO;
		IPath[] children = workspace.getElementTree().getChildren(path);
		for (int i = 0; i < children.length; i++) {
			max = Math.max(max, recursiveFindMaxSeverity(children[i], type, includeSubtypes, depth));
			if (max >= IMarker.SEVERITY_ERROR) {
				break;
			}
		}
		return max;
	}

	/**
	 * Adds the markers for a subtree of resources to the list.
	 */
	private void recursiveRemoveMarkers(final IPath path, String type, boolean includeSubtypes, int depth) {
		ResourceInfo info = workspace.getResourceInfo(path, false, false);
		if (info == null)//phantoms don't have markers
			return;
		IPathRequestor requestor = new IPathRequestor() {
			public String requestName() {
				return path.lastSegment();
			}

			public IPath requestPath() {
				return path;
			}
		};
		basicRemoveMarkers(info, requestor, type, includeSubtypes);
		//recurse
		if (depth == IResource.DEPTH_ZERO || info.getType() == IResource.FILE)
			return;
		if (depth == IResource.DEPTH_ONE)
			depth = IResource.DEPTH_ZERO;
		IPath[] children = workspace.getElementTree().getChildren(path);
		for (int i = 0; i < children.length; i++) {
			recursiveRemoveMarkers(children[i], type, includeSubtypes, depth);
		}
	}

	/**
	 * Removes the specified marker 
	 */
	public void removeMarker(IResource resource, long id) {
		MarkerInfo markerInfo = findMarkerInfo(resource, id);
		if (markerInfo == null)
			return;
		ResourceInfo info = ((Workspace) resource.getWorkspace()).getResourceInfo(resource.getFullPath(), false, true);
		//Concurrency: copy the marker set on modify
		MarkerSet markers = info.getMarkers(true);
		int size = markers.size();
		markers.remove(markerInfo);
		// if that was the last marker remove the set to save space.
		info.setMarkers(markers.size() == 0 ? null : markers);
		// if we actually did remove a marker, post a delta for the change.
		if (markers.size() != size) {
			if (isPersistent(markerInfo))
				info.set(ICoreConstants.M_MARKERS_SNAP_DIRTY);
			IMarkerSetElement[] change = new IMarkerSetElement[] {new MarkerDelta(IResourceDelta.REMOVED, resource, markerInfo)};
			changedMarkers(resource, change);
		}
	}

	/**
	 * Remove all markers for the given resource to the specified depth.
	 */
	public void removeMarkers(IResource resource, int depth) {
		removeMarkers(resource, null, false, depth);
	}

	/**
	 * Remove all markers with the given type from the node at the given path.
	 * Passing <code>null</code> for the type specifies a match
	 * for all types (i.e., <code>null</code> is a wildcard.
	 */
	public void removeMarkers(IResource target, final String type, final boolean includeSubtypes, int depth) {
		if (depth == IResource.DEPTH_INFINITE && target.getType() != IResource.FILE)
			visitorRemoveMarkers(target.getFullPath(), type, includeSubtypes);
		else
			recursiveRemoveMarkers(target.getFullPath(), type, includeSubtypes, depth);
	}

	/**
	 * Reset the marker deltas up to but not including the given start Id.
	 */
	public void resetMarkerDeltas(long startId) {
		currentDeltas = null;
		deltaManager.resetDeltas(startId);
	}

	public void restore(IResource resource, boolean generateDeltas, IProgressMonitor monitor) throws CoreException {
		// first try and load the last saved file, then apply the snapshots
		restoreFromSave(resource, generateDeltas);
		restoreFromSnap(resource);
	}

	protected void restoreFromSave(IResource resource, boolean generateDeltas) throws CoreException {
		IPath sourceLocation = workspace.getMetaArea().getMarkersLocationFor(resource);
		IPath tempLocation = workspace.getMetaArea().getBackupLocationFor(sourceLocation);
		java.io.File sourceFile = new java.io.File(sourceLocation.toOSString());
		java.io.File tempFile = new java.io.File(tempLocation.toOSString());
		if (!sourceFile.exists() && !tempFile.exists())
			return;
		try {
			DataInputStream input = new DataInputStream(new SafeFileInputStream(sourceLocation.toOSString(), tempLocation.toOSString()));
			try {
				MarkerReader reader = new MarkerReader(workspace);
				reader.read(input, generateDeltas);
			} finally {
				input.close();
			}
		} catch (Exception e) {
			//don't let runtime exceptions such as ArrayIndexOutOfBounds prevent startup
			String msg = NLS.bind(Messages.resources_readMeta, sourceLocation);
			throw new ResourceException(IResourceStatus.FAILED_READ_METADATA, sourceLocation, msg, e);
		}
	}

	protected void restoreFromSnap(IResource resource) {
		IPath sourceLocation = workspace.getMetaArea().getMarkersSnapshotLocationFor(resource);
		if (!sourceLocation.toFile().exists())
			return;
		try {
			DataInputStream input = new DataInputStream(new SafeChunkyInputStream(sourceLocation.toFile()));
			try {
				MarkerSnapshotReader reader = new MarkerSnapshotReader(workspace);
				while (true)
					reader.read(input);
			} catch (EOFException eof) {
				// ignore end of file
			} finally {
				input.close();
			}
		} catch (Exception e) {
			// only log the exception, we should not fail restoring the snapshot
			String msg = NLS.bind(Messages.resources_readMeta, sourceLocation);
			Policy.log(new ResourceStatus(IResourceStatus.FAILED_READ_METADATA, sourceLocation, msg, e));
		}
	}

	public void save(ResourceInfo info, IPathRequestor requestor, DataOutputStream output, List list) throws IOException {
		writer.save(info, requestor, output, list);
	}

	/* (non-Javadoc)
	 * @see IManager#shutdown(IProgressMonitor)
	 */
	public void shutdown(IProgressMonitor monitor) {
		// do nothing
	}

	public void snap(ResourceInfo info, IPathRequestor requestor, DataOutputStream output) throws IOException {
		writer.snap(info, requestor, output);
	}

	/* (non-Javadoc)
	 * @see IManager#startup(IProgressMonitor)
	 */
	public void startup(IProgressMonitor monitor) {
		// do nothing
	}

	/**
	 * Adds the markers for a subtree of resources to the list.
	 */
	private void visitorFindMarkers(IPath path, final ArrayList list, final String type, final boolean includeSubtypes) {
		IElementContentVisitor visitor = new IElementContentVisitor() {
			public boolean visitElement(ElementTree tree, IPathRequestor requestor, Object elementContents) {
				ResourceInfo info = (ResourceInfo) elementContents;
				if (info == null)
					return false;
				MarkerSet markers = info.getMarkers(false);

				//add the matching markers for this resource
				if (markers != null) {
					IMarkerSetElement[] matching;
					if (type == null)
						matching = markers.elements();
					else
						matching = basicFindMatching(markers, type, includeSubtypes);
					buildMarkers(matching, requestor.requestPath(), info.getType(), list);
				}
				return true;
			}
		};
		new ElementTreeIterator(workspace.getElementTree(), path).iterate(visitor);
	}

	/**
	 * Finds the max severity across problem markers for a subtree of resources.
	 */
	private int visitorFindMaxSeverity(IPath path, final String type, final boolean includeSubtypes) {
		class MaxSeverityVisitor implements IElementContentVisitor {
			int max = -1;

			public boolean visitElement(ElementTree tree, IPathRequestor requestor, Object elementContents) {
				// bail if an earlier sibling already hit the max
				if (max >= IMarker.SEVERITY_ERROR) {
					return false;
				}
				ResourceInfo info = (ResourceInfo) elementContents;
				if (info == null)
					return false;
				MarkerSet markers = info.getMarkers(false);

				//add the matching markers for this resource
				if (markers != null) {
					max = Math.max(max, basicFindMaxSeverity(markers, type, includeSubtypes));
				}
				return max < IMarker.SEVERITY_ERROR;
			}
		}
		MaxSeverityVisitor visitor = new MaxSeverityVisitor();
		new ElementTreeIterator(workspace.getElementTree(), path).iterate(visitor);
		return visitor.max;
	}

	/**
	 * Adds the markers for a subtree of resources to the list.
	 */
	private void visitorRemoveMarkers(IPath path, final String type, final boolean includeSubtypes) {
		IElementContentVisitor visitor = new IElementContentVisitor() {
			public boolean visitElement(ElementTree tree, IPathRequestor requestor, Object elementContents) {
				ResourceInfo info = (ResourceInfo) elementContents;
				if (info == null)
					return false;
				basicRemoveMarkers(info, requestor, type, includeSubtypes);
				return true;
			}
		};
		new ElementTreeIterator(workspace.getElementTree(), path).iterate(visitor);
	}
}
