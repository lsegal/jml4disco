package org.jmlspecs.jml2.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;

public class Util {
	/* (non-Javadoc)
	 * @see org.jmlspecs.eclipse.jdt.core.EscJava2BatchWrapper#translatePath(java.lang.String)
	 */
	// This implementation anticipates that fileName is a workspace-absolute
	// path and translates it into an absolute file system path suitable for
	// ESCTools
	// FIXME test that this is correct if the file system path contains a link
	// FIXME should this use toOSString and use paths? Does this work correctly
	// on all platforms?
	public static String translatePath(String fileName) {
		IWorkspace workspace = null;
		try {
			workspace = ResourcesPlugin.getWorkspace();
		} catch (IllegalStateException e) {
			/* ignored */
		}
		if (workspace != null) { // we got a workspace so it is safe to obtain
									// its absolute location
			IFile f = workspace.getRoot().getFile(new Path(fileName));
			fileName = f.getRawLocation().toString();
		}
		return fileName;
	}

	public static/*@nullable*/String exec(String[] cmd) {
		String result = null;
		Runtime rt = Runtime.getRuntime();
		try {
			Process p = rt.exec(cmd);
			p.waitFor();
			InputStreamReader isr = new InputStreamReader(p.getErrorStream());
			BufferedReader in = new BufferedReader(isr);
			String line;
			result = ""; //$NON-NLS-1$
			while (null != (line = in.readLine())) {
				result += line + "\n"; //$NON-NLS-1$
			}
			in.close();
		} catch (IOException e) {
			result = e.toString();
			e.printStackTrace();
		} catch (InterruptedException e) {
			result = e.toString();
			e.printStackTrace();
		}
		return result;
	}

	public static int getSourceStart(int[] lineEnds, int line, int column) {
		int result = 0;
		if (line == 1)
			result = column;
		else
			result = lineEnds[line - 2] + column;
		return result;
	}

	public static int getSourceStartOfLine(int[] lineEnds, int line) {
		int result = 0;
		if (line <= 1)
			result = 0;
		else if (line - 2 < lineEnds.length)
			result = lineEnds[line - 2] + 1;
		return result;
	}

	public static int getSourceEndOfLine(int[] lineEnds, int line) {
		int result = line < 1 || line - 1 >= lineEnds.length
			? 0
			: lineEnds[line - 1];
		return result;
	}

	public static /*@nullable*/ String projectRawPathOf(String fileName) {
		IWorkspace workspace = null;
		String result = null;
		try {
			workspace = ResourcesPlugin.getWorkspace();
		} catch (IllegalStateException e) {
			/* ignored */
		}
		if (workspace != null) { // we got a workspace so it is safe to obtain
									// its absolute location
			IFile f = workspace.getRoot().getFile(new Path(fileName));
			IProject p = f.getProject();
			result = p.getLocation().toString();
		}
		return result;
	}
}
