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
package org.eclipse.core.internal.watson;

/**
 * This is what you would expect for an element tree comparator.
 * Clients of the element tree that want specific comparison behaviour
 * must define their own element comparator (without subclassing or
 * otherwise extending this comparator).  Internal element tree operations 
 * rely on the behaviour of this type, and the ElementTree maintainer 
 * reserves the right to change its behaviour as necessary.
 */
public final class DefaultElementComparator implements IElementComparator {
	private static DefaultElementComparator singleton;

	/**
	 * Force clients to use the singleton
	 */
	protected DefaultElementComparator() {
		super();
	}

	/**
	 * Returns the type of change.
	 */
	public int compare(Object oldInfo, Object newInfo) {
		if (oldInfo == null && newInfo == null)
			return 0;
		if (oldInfo == null || newInfo == null)
			return 1;
		return testEquality(oldInfo, newInfo) ? 0 : 1;
	}

	/**
	 * Returns the singleton instance
	 */
	public static IElementComparator getComparator() {
		if (singleton == null) {
			singleton = new DefaultElementComparator();
		}
		return singleton;
	}

	/**
	 * Makes a comparison based on equality
	 */
	protected boolean testEquality(Object oldInfo, Object newInfo) {
		if (oldInfo == null && newInfo == null)
			return true;
		if (oldInfo == null || newInfo == null)
			return false;

		return oldInfo.equals(newInfo);
	}
}
