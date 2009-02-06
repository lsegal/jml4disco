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
package org.eclipse.core.internal.utils;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * An object that iterates over the elements of an array
 */
public class ArrayIterator implements Iterator {
	Object[] elements;
	int index;
	int lastElement;

	/**
	 * Returns new array enumeration over the given object array
	 */
	public ArrayIterator(Object[] elements) {
		this(elements, 0, elements.length - 1);
	}

	/**
	 * Returns new array enumeration over the given object array
	 */
	public ArrayIterator(Object[] elements, int firstElement, int lastElement) {
		super();
		this.elements = elements;
		index = firstElement;
		this.lastElement = lastElement;
	}

	/**
	 * Returns true if this enumeration contains more elements.
	 */
	public boolean hasNext() {
		return elements != null && index <= lastElement;
	}

	/**
	 * Returns the next element of this enumeration.
	 * @exception  NoSuchElementException  if no more elements exist.
	 */
	public Object next() throws NoSuchElementException {
		if (!hasNext())
			throw new NoSuchElementException();
		return elements[index++];
	}

	public void remove() {
		throw new UnsupportedOperationException();
	}
}
