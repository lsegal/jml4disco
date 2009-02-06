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
package org.eclipse.core.internal.utils;

import java.io.UnsupportedEncodingException;

public class Convert {

	/**
	 * Converts the string argument to a byte array.
	 */
	public static String fromUTF8(byte[] b) {
		String result;
		try {
			result = new String(b, "UTF8"); //$NON-NLS-1$
		} catch (UnsupportedEncodingException e) {
			result = new String(b);
		}
		return result;
	}

	/**
	 * Converts the string argument to a byte array.
	 */
	public static byte[] toUTF8(String s) {
		byte[] result;
		try {
			result = s.getBytes("UTF8"); //$NON-NLS-1$
		} catch (UnsupportedEncodingException e) {
			result = s.getBytes();
		}
		return result;
	}

	/**
	 * Performs conversion of a long value to a byte array representation.
	 *
	 * @see #bytesToLong(byte[])
	 */
	public static byte[] longToBytes(long value) {

		// A long value is 8 bytes in length.
		byte[] bytes = new byte[8];

		// Convert and copy value to byte array:
		//   -- Cast long to a byte to retrieve least significant byte;
		//   -- Left shift long value by 8 bits to isolate next byte to be converted;
		//   -- Repeat until all 8 bytes are converted (long = 64 bits).
		// Note: In the byte array, the least significant byte of the long is held in
		// the highest indexed array bucket.

		for (int i = 0; i < bytes.length; i++) {
			bytes[(bytes.length - 1) - i] = (byte) value;
			value >>>= 8;
		}

		return bytes;
	}

	/**
	 * Performs conversion of a byte array to a long representation.
	 *
	 * @see #longToBytes(long)
	 */
	public static long bytesToLong(byte[] value) {

		long longValue = 0L;

		// See method convertLongToBytes(long) for algorithm details.	
		for (int i = 0; i < value.length; i++) {
			// Left shift has no effect thru first iteration of loop.
			longValue <<= 8;
			longValue ^= value[i] & 0xFF;
		}

		return longValue;
	}
}
