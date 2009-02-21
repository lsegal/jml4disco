package org.jmlspecs.eclipse.jdt.core.tests.util;

import java.io.File;
import java.io.IOException;

import org.eclipse.jdt.core.tests.util.Util;

public class JmlCoreTestsUtil {
	
	/** Like <code>org.eclipse.jdt.core.tests.util.Util.flushDirectoryContent()</code>
	 * except that we do not flush the sourcePath first.
	 */
	public static void createSourceDir(String[] pathsAndContents, String sourcesPath) throws IOException {
	    for (int i = 0, length = pathsAndContents.length; i < length; i+=2) {
	        String sourcePath = sourcesPath + File.separator + pathsAndContents[i];
	        File sourceFile = new File(sourcePath);
	        sourceFile.getParentFile().mkdirs();
	        Util.createFile(sourcePath, pathsAndContents[i+1]);
	    }
	}

	public static String defaultJavaExtension() {
		return org.eclipse.jdt.internal.core.util.Util.defaultJavaExtension();
	}
}
