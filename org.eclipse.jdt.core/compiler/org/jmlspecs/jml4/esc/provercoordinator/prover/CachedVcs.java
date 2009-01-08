package org.jmlspecs.jml4.esc.provercoordinator.prover;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.jmlspecs.jml2.util.Util;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class CachedVcs {

	private final Set/*<String>*/ allVcs  = new HashSet/*<String>*/();
	private final Set/*<String>*/ usedVcs = new HashSet/*<String>*/();
	public final String filename;
	private static final String EXTENSION = ".vcs"; //$NON-NLS-1$
	
	public CachedVcs(CompilationUnitDeclaration unit) {
		this.filename = getVcFilename(unit);
		readVcFile();
	}
	private String getVcFilename(CompilationUnitDeclaration unit) {
		// FIXME: put the vc file somewhere other than the src
		String javaFilename = new String(unit.compilationResult().getFileName());
		javaFilename = Util.translatePath(javaFilename);
		javaFilename = Utils.win2unixFileName(javaFilename);
//		if (javaFilename.startsWith(File.separator) || javaFilename.startsWith("/")) { //$NON-NLS-1$
//			// FIXME: use project root instead ...
//			String pathPrefix = "JML4VCCache"; //$NON-NLS-1$
//			javaFilename = pathPrefix + javaFilename;
//		}
		String dotJava = ".java"; //$NON-NLS-1$
		int baseLength = javaFilename.length() - dotJava.length();
		String base = javaFilename.substring(0, baseLength);
		return base + EXTENSION;
	}
	private void readVcFile() {
		BufferedReader in = null;
		try {
			File file = new File(this.filename);
			if (! file.exists())
				return;
			in = new BufferedReader(new FileReader(file));
			String line;
			while ((line=in.readLine()) != null) {
				allVcs.add(line.intern());
			}
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			try {
				if (in != null)
					in.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	public void writeToDisk() throws IOException {
		if (this.usedVcs.size() == 0) {
			File file = new File(this.filename);
			if (file.exists())
				file.delete();
		} else {
			PrintWriter out = null;
			try {
                File file = new File(this.filename);
                File dir = file.getParentFile();
                if (dir != null)
                	dir.mkdirs();
                out = new PrintWriter(new FileWriter(file));
                for (Iterator iterator = usedVcs.iterator(); iterator.hasNext();) {
					String sVc = (String) iterator.next();
					out.println(sVc);
				}
			} finally {
				if (out != null)
					out.close();
			}
		}
	}
	public boolean contains(VcProgram vc) {
		return contains(vc.toString().intern());
	}
	public boolean contains(VC vc) {
		return contains(vc.toString().intern());
	}
	public boolean contains(String s) {
		s = s.replace('\n', ' ');
		if (this.allVcs.contains(s)) {
			this.usedVcs.add(s);
			return true;
		}
		return false;
	}
	public void add(VcProgram vc) {
		add(vc.toString().intern());
	}
	public void add(VC vc) {
		add(vc.toString().intern());
	}
	public void add(String s) {
		s = s.replace('\n', ' ');
		this.allVcs.add(s);
		this.usedVcs.add(s);
	}
}
