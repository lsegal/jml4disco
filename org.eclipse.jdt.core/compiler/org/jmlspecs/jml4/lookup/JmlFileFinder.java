package org.jmlspecs.jml4.lookup;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.batch.FileSystem;
import org.eclipse.jdt.internal.compiler.batch.JmlFileSystem;
import org.eclipse.jdt.internal.compiler.env.INameEnvironment;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.core.builder.NameEnvironment;



public class JmlFileFinder {
	private final static String EMPTY_STRING_ARRAY[] = new String[0];
	private final static FileSystem EMPTY_FILE_SYS = new FileSystem(EMPTY_STRING_ARRAY, EMPTY_STRING_ARRAY, ""); //$NON-NLS-1$

	public final INameEnvironment sourceNameEnv;
	// private INameEnvironment spenNameEnv = EMPTY_FILE_SYS;
	
	private final File[] sourcePath;
	private       File[] specPath;

	// TODO: Can the compilerOption's specPath change during the lifetime of this?
	//       If not, remove the compilerOptions field and related methods.
	private final CompilerOptions compilerOptions;
	private       String sSpecPath;
	
	private static final String sourceSuffix = ".java"; //$NON-NLS-1$
	private static final String[] specSuffixes = { ".jml", ".spec", ".refines-java", ".refines-spec", ".refines-jml" }; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$ //$NON-NLS-5$
	private static final char pathSeperator = File.pathSeparatorChar;
	private static final char fileSeperator = File.separatorChar;
	private static final File[] emptyFileArray = new File[0];
	private static final boolean DEBUG = false;

	public JmlFileFinder(Compiler compiler) {
		// TODO: make sure the source & class paths are flushed when the spec path is
		this.compilerOptions = compiler.options;
		this.sSpecPath = this.compilerOptions.jmlSpecPath;
		if (!this.compilerOptions.jmlEnabled) {
			this.specPath = emptyFileArray;
			this.sourcePath = emptyFileArray;
			this.sourceNameEnv = EMPTY_FILE_SYS;
			return;
		}

		this.specPath = getDirsInPath(this.sSpecPath);

		INameEnvironment iNameEnvironment= compiler.lookupEnvironment.nameEnvironment;
		//TODO: consider changing the ref to NameEnvironment below
		//      to a JML-specific subclass that has these 2 methods
		if (iNameEnvironment instanceof NameEnvironment) {
			NameEnvironment nameEnvironment = (NameEnvironment) iNameEnvironment;
			this.sourcePath = strings2files(nameEnvironment.getSourcePath());
			this.sourceNameEnv = JmlFileSystem.make(nameEnvironment.getSourcePath());
		} else if (iNameEnvironment instanceof FileSystem) {
			this.sourceNameEnv = JmlFileSystem.make((FileSystem)iNameEnvironment);
			this.sourcePath = emptyFileArray;
		} else {
			this.sourceNameEnv = EMPTY_FILE_SYS;
			this.sourcePath = emptyFileArray;
		}
	}
	
	private File[] strings2files(String[] path) {
		List list = new ArrayList(path.length);
		for (int i=0, length=path.length; i < length; i++) {
			String filename = path[i];
			if (filename.indexOf('*') > 0)
				filename = filename.substring(0, filename.lastIndexOf(fileSeperator));
			File file = new File(path[i]);
			if (file.exists())
				list.add(file);
		}
		return (File[])list.toArray(new File[0]);
	}
	
	private File[] getDirsInPath(String path) {
		String[] items = ((path == null) ? "." : path).split(""+pathSeperator); //$NON-NLS-1$ //$NON-NLS-2$
		List result = new ArrayList();
		for (int i = 0; i < items.length; i++) {
			File file = new File(items[i]);
			if (file.exists())
				result.add(file);
		}
		return (File[]) result.toArray(emptyFileArray);
	}
	
	private void checkSpecPathForUpdate() {
		if (this.sSpecPath != this.compilerOptions.jmlSpecPath) {
			this.sSpecPath = this.compilerOptions.jmlSpecPath;
			this.specPath = this.sSpecPath == null ? emptyFileArray : getDirsInPath(this.sSpecPath);
		}
	}
	
	public File[] find(char[] name) {
		checkSpecPathForUpdate();
		return find(new String(name));
	}
	
	public File[] find(String name) {
		checkSpecPathForUpdate();
		File[] source = findSource(name);
		File[] specs = findSpecs(name);
		File[] result = new File[specs.length + source.length];
		System.arraycopy(source, 0, result, 0, source.length);
		System.arraycopy(specs,  0, result, source.length, specs.length);
		return result;
	}
	
	public File[] findSource(String name) {
		File[] result = find(name + sourceSuffix, this.sourcePath);
		if (DEBUG) { 
			for (int i=0; i<result.length; i++)
				System.out.println("adding source file '"+result[i].getAbsolutePath()+"'");  //$NON-NLS-1$//$NON-NLS-2$
		}
		// char[][] compoundTypeName = null;
		// this.sourceNameEnv.findType(compoundTypeName).getCompilationUnit();
		return result;
	}
	
	public File[] findSpecs(String name) {
		checkSpecPathForUpdate();
		List result = new ArrayList();
		for (int i = 0; i < specSuffixes.length; i++) {
			File[] specFiles = find(name+specSuffixes[i], this.specPath);
			for (int j = 0; j < specFiles.length; j++) {
				if (DEBUG) System.out.println("adding spec file '"+specFiles[j].getAbsolutePath()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
				result.add(specFiles[j]);
			}
		}
/*		if (name.indexOf("Main") >= 0) { //$NON-NLS-1$
			Logger.println("found "+result.size()+" files for "+name); //$NON-NLS-1$ //$NON-NLS-2$
			if (result.size() > 0) {
				try {
				Logger.println("first is "+((File)(result.get(0))).getCanonicalPath()); //$NON-NLS-1$
				} catch (IOException ioe) {
					
				}
			}
		}
*/
		return (File[]) result.toArray(emptyFileArray);
	}

	public static File[] find(String name, File[] paths) {
		List result = new ArrayList();
		for (int i = 0; i < paths.length; i++) {
			File file = new File(paths[i], name);
			if (file.exists())
				result.add(file);
		}
		return (File[]) result.toArray(emptyFileArray);
	}
}
