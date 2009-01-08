package org.jmlspecs.jml4.esc.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Set;

public class Utils {

    public static void assertTrue(boolean b, String msg) {
		if (!b)
			throw new RuntimeException(msg);
	}

    public static void assertNotNull(Object o) {
		assertNotNull(o, "AssertNotNull failed"); //$NON-NLS-1$
	}

	public static void assertNotNull(Object o, String msg) {
		if (o == null)
			throw new RuntimeException(msg);
	}

	public static int max(Set/*<Integer>*/ set) {
		return max((Integer[])set.toArray(new Integer[0]));
	}
	public static int max(Integer[] array) {
		int result = 0;
		for (int i = 0; i < array.length; i++) {
			int val = array[i].intValue();
			if (val > result)
				result = val;
		}
		return result;
	}
	//TODO Java5: replace uses of the following method with calls to the one in Arrays
	public static String toString(Object[] a) {
		if (a==null)
			return "null"; //$NON-NLS-1$
		StringBuffer result = new StringBuffer();
		result.append('[');
		for (int i = 0; i < a.length; i++) {
			if (i > 0)
				result.append(", "); //$NON-NLS-1$
			result.append(a[i].toString());
		}
		result.append(']');
		return result.toString();
	}
	public static String toString(char[][] a, char separator) {
		if (a==null)
			return "null"; //$NON-NLS-1$
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < a.length; i++) {
			if (i > 0)
				result.append(separator);
			result.append(new String(a[i]));
		}
		return result.toString();
	}
	// the following code is based on some found in Sun's Integer class
	public static Integer valueOf(int i) {
    	if (0 <= i && i <= 127) {
    	    return cache[i];
    	}
        return new Integer(i);
    }

	public static int parseInt(String s, int defaultValue) {
		int result;
		try {
			result = Integer.parseInt(s);
		} catch (NumberFormatException nfe) {
			result = defaultValue;
		}
		return result;
	}

	private static final Integer cache[] = new Integer[128];
    static {
    	for(int i = 0; i < cache.length; i++)
    	cache[i] = new Integer(i);
    }
	public static void writeToFile(String filename, String isabelleString) {
		FileWriter out = null;
		try {
			File file = new File(filename);
			File dir = file.getParentFile();
			if (dir != null && !dir.exists()) {
				dir.mkdirs();
			}
			out = new FileWriter(filename);
			out.write(isabelleString);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (out != null) {
			try {
				out.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
	public static String readFromFile(String filename) {
		StringBuffer result= new StringBuffer();
		BufferedReader in = null;
		try {
			in = new BufferedReader(new FileReader(filename));
			String line;
			while (null != (line = in.readLine()))
				result.append(line + "\n"); //$NON-NLS-1$
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} finally {
			if (in != null) {
				try { in.close(); }
				catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		return result.toString();
	}
	public static void deleteFile(String filename) {
		File file = new File(filename);
		file.delete();
	}
	
	public static String win2unixFileName(String filename) {
		String unixFilename = filename.replace('\\', '/');
		// Strip off drive letter, "C:"
		if(filename.length() >= 2 && filename.charAt(1) == ':') {
			unixFilename = unixFilename.substring(2);
		}
		return unixFilename;
	}
}
