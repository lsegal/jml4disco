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

import java.io.UnsupportedEncodingException;
import java.util.Map;
import org.eclipse.core.internal.utils.IStringPoolParticipant;
import org.eclipse.core.internal.utils.StringPool;
import org.eclipse.core.runtime.Assert;

public class MarkerInfo implements IMarkerSetElement, Cloneable, IStringPoolParticipant {

	// well known Integer values
	protected static final Integer INTEGER_ONE = new Integer(1);
	protected static final Integer INTEGER_TWO = new Integer(2);
	protected static final Integer INTEGER_ZERO = new Integer(0);
	
	//
	protected static final long UNDEFINED_ID = -1;
	/** The store of attributes for this marker. */
	protected Map attributes = null;

	/** The creation time for this marker. */
	protected long creationTime = 0;

	/** Marker identifier. */
	protected long id = UNDEFINED_ID;

	/** The type of this marker. */
	protected String type = null;

	/**
	 * Returns whether the given object is a valid attribute value. Returns
	 * either the attribute or an equal canonical substitute.
	 */
	protected static Object checkValidAttribute(Object value) {
		if (value == null)
			return null;
		if (value instanceof String) {
			//we cannot write attributes whose UTF encoding exceeds 65535 bytes.
			String valueString = (String) value;
			//optimized test based on maximum 3 bytes per character
			if (valueString.length() < 21000)
				return value;
			byte[] bytes;
			try {
				bytes = valueString.getBytes(("UTF-8"));//$NON-NLS-1$
			} catch (UnsupportedEncodingException uee) {
				//cannot validate further
				return value;
			}
			if (bytes.length > 65535) {
				String msg = "Marker property value is too long: " + valueString.substring(0, 10000); //$NON-NLS-1$
				Assert.isTrue(false, msg);
			}
			return value;
		}
		if (value instanceof Boolean) {
			//return canonical boolean
			return ((Boolean) value).booleanValue() ? Boolean.TRUE : Boolean.FALSE;
		}
		if (value instanceof Integer) {
			//replace common integers with canonical values
			switch (((Integer) value).intValue()) {
				case 0 :
					return INTEGER_ZERO;
				case 1 :
					return INTEGER_ONE;
				case 2 :
					return INTEGER_TWO;
			}
			return value;
		}
		//if we got here, it's an invalid attribute value type
		throw new IllegalArgumentException();
	}

	public MarkerInfo() {
		super();
	}

	/**
	 * See Object#clone.
	 */
	public Object clone() {
		try {
			MarkerInfo copy = (MarkerInfo) super.clone();
			//copy the attribute table contents
			copy.attributes = getAttributes(true);
			return copy;
		} catch (CloneNotSupportedException e) {
			//cannot happen because this class implements Cloneable
			return null;
		}
	}

	public Object getAttribute(String attributeName) {
		return attributes == null ? null : attributes.get(attributeName);
	}

	public Map getAttributes() {
		return getAttributes(true);
	}

	public Map getAttributes(boolean makeCopy) {
		if (attributes == null)
			return null;
		return makeCopy ? new MarkerAttributeMap(attributes) : attributes;
	}

	public Object[] getAttributes(String[] attributeNames) {
		Object[] result = new Object[attributeNames.length];
		for (int i = 0; i < attributeNames.length; i++)
			result[i] = getAttribute(attributeNames[i]);
		return result;
	}

	public long getCreationTime() {
		return creationTime;
	}

	public long getId() {
		return id;
	}

	public String getType() {
		return type;
	}

	public void internalSetAttributes(Map map) {
		//the cast effectively acts as an assertion to make sure
		//the right kind of map is being used
		attributes = map;
	}

	public void setAttribute(String attributeName, Object value) {
		value = checkValidAttribute(value);
		if (attributes == null) {
			if (value == null)
				return;
			attributes = new MarkerAttributeMap();
			attributes.put(attributeName, value);
		} else {
			if (value == null) {
				attributes.remove(attributeName);
				if (attributes.isEmpty())
					attributes = null;
			} else {
				attributes.put(attributeName, value);
			}
		}
	}

	public void setAttributes(Map map) {
		if (map == null)
			attributes = null;
		else
			attributes = new MarkerAttributeMap(map);
	}

	public void setAttributes(String[] attributeNames, Object[] values) {
		Assert.isTrue(attributeNames.length == values.length);
		for (int i = 0; i < attributeNames.length; i++)
			setAttribute(attributeNames[i], values[i]);
	}

	public void setCreationTime(long value) {
		creationTime = value;
	}

	public void setId(long value) {
		id = value;
	}

	public void setType(String value) {
		type = value;
	}

	/* (non-Javadoc
	 * Method declared on IStringPoolParticipant
	 */
	public void shareStrings(StringPool set) {
		type = set.add(type);
		Map map = attributes;
		if (map instanceof IStringPoolParticipant)
			((IStringPoolParticipant) map).shareStrings(set);
	}
}
