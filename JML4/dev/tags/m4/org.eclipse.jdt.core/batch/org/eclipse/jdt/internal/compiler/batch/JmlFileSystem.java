package org.eclipse.jdt.internal.compiler.batch;

/**
 * Instances of this class are useful for looking up source files.
 * A JmlFileSystem is like a FileSystem except that findType() will return
 * source files rather than binary files.
 * 
 */
public class JmlFileSystem extends FileSystem {
	
	public JmlFileSystem(Classpath[] paths, /*@nullable*/String[] initialFileNames) {
		super(paths, initialFileNames);
	}

	public static JmlFileSystem make(FileSystem fileSystem) {
		Classpath[] cps = getClassPathsFromFileSystem(fileSystem);
		String[] initialFileNames = (String[]) fileSystem.knownFileNames.toArray(new String[0]);
		return new JmlFileSystem(cps, initialFileNames);
	}

	public static JmlFileSystem make(String[] sourcePath) {
		Classpath[] cps = helper(sourcePath);
		return new JmlFileSystem(cps, null);
	}

	private static Classpath[] helper(String[] sourcePath) {
		int numClasspaths = sourcePath == null ? 0 : sourcePath.length;
		Classpath[] result = new FileSystem.Classpath[numClasspaths];

		for (int i = 0; i < numClasspaths; i++) {
			// FIXME: what should we use for encoding, accessRuleSet and
			// destinationPath of the classpath?
			result[i] = FileSystem.getClasspath(sourcePath[i],
			/* encoding */null,
			/* isSourceOnly */true,
			/* accessRuleSet */null,
			/* destinationPath */null);
		}
		return result;
	}

	private static Classpath[] getClassPathsFromFileSystem(FileSystem fileSystem) {
		int numClasspaths = fileSystem.classpaths == null ? 0
				: fileSystem.classpaths.length;
		Classpath[] result = new FileSystem.Classpath[numClasspaths];

		for (int i = 0; i < numClasspaths; i++) {
			// FIXME: should use the original encoding, accessRuleSet and
			// destinationPath of the classpath
			result[i] = FileSystem.getClasspath(fileSystem.classpaths[i]
					.getPath(),
			/* encoding */null,
			/* isSourceOnly */true,
			/* accessRuleSet */null,
			/* destinationPath */null);
		}
		return result;
	}

}
