/*******************************************************************************
 * Copyright (c) 2003, 2005 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM - Initial API and implementation
 *******************************************************************************/
package org.eclipse.core.internal.resources;

import java.util.*;

/**
 * The notification mechanism can request marker deltas for several overlapping intervals
 * of time. This class maintains a history of marker deltas, and upon request can
 * generate a map of marker deltas for any interval.  This is done by maintaining 
 * batches of marker deltas keyed by the change Id at the start of that batch.
 * When the delta factory requests a delta, it specifies the start generation, and
 * this class assembles the deltas for all generations between then and the most
 * recent delta.
 */
class MarkerDeltaManager {
	private static final int DEFAULT_SIZE = 10;
	private long[] startIds = new long[DEFAULT_SIZE];
	private Map[] batches = new Map[DEFAULT_SIZE];
	private int nextFree = 0;

	/**
	 * Returns the deltas from the given start id up until the present. Returns null
	 * if there are no deltas for that interval.
	 */
	protected Map assembleDeltas(long start) {
		Map result = null;
		for (int i = 0; i < nextFree; i++)
			if (startIds[i] >= start)
				result = MarkerDelta.merge(result, batches[i]);
		return result;
	}

	/**
	 * Flushes all delta batches up to but not including the given start Id.
	 */
	protected void resetDeltas(long startId) {
		//find offset of first batch to keep
		int startOffset = 0;
		for (; startOffset < nextFree; startOffset++)
			if (startIds[startOffset] >= startId)
				break;
		if (startOffset == 0)
			return;
		long[] newIds = startIds;
		Map[] newBatches = batches;
		//shrink the arrays if it has grown too large
		if (startIds.length > DEFAULT_SIZE && (nextFree - startOffset < DEFAULT_SIZE)) {
			newIds = new long[DEFAULT_SIZE];
			newBatches = new Map[DEFAULT_SIZE];
		}
		//copy and compact into the new array
		int remaining = nextFree - startOffset;
		System.arraycopy(startIds, startOffset, newIds, 0, remaining);
		System.arraycopy(batches, startOffset, newBatches, 0, remaining);
		//clear the end of the array
		Arrays.fill(startIds, remaining, startIds.length, 0);
		Arrays.fill(batches, remaining, startIds.length, null);
		startIds = newIds;
		batches = newBatches;
		nextFree = remaining;
	}

	protected Map newGeneration(long start) {
		int len = startIds.length;
		if (nextFree >= len) {
			long[] newIds = new long[len * 2];
			Map[] newBatches = new Map[len * 2];
			System.arraycopy(startIds, 0, newIds, 0, len);
			System.arraycopy(batches, 0, newBatches, 0, len);
			startIds = newIds;
			batches = newBatches;
		}
		startIds[nextFree] = start;
		batches[nextFree] = new HashMap(11);
		return batches[nextFree++];
	}
}
