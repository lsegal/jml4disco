package org.jmlspecs.eclipse.jdt.core.tests.jml2;

import java.io.File;
import java.io.IOException;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.eclipse.jdt.core.tests.util.JmlCoreTestsUtil;
import org.jmlspecs.eclipse.jdt.core.tests.util.JmlTestCase;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class JML2TestCase extends JmlTestCase {
	
	public JML2TestCase(String name) {
		super(name);
	}

	// Augment problem detection settings
	@Override
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
		Map<String, String> options = super.getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_EnableJml2Checker, CompilerOptions.ENABLED);
		return options;
	}

	public void test_0001_JML2Sanity() throws IOException {
		String source_X = 
			"public class X {\n" +
			"  //@ invariant true;\n" + 
			"  public void m() {}\n" + 
			"}\n";
		String xPath = "X.java";
		String[] pathAndContents = new String[] {
				xPath,
				source_X
		};
		JmlCoreTestsUtil.createSourceDir(pathAndContents, SOURCE_DIRECTORY);
		String srcPath = ""; // must be blank for bug to show, otherwise
		String destDir = SOURCE_DIRECTORY; // use source as destination for .class files.
		String result;
		String expected = "";
		System.setProperty("jdt.compiler.useSingleThread", "true");
    	String batchCompilerOptions = "-jml2";
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + xPath, srcPath, destDir);
		assertEquals(xPath + ": " + result, expected, result); 
	}

	public void test_0002_JML2Sanity() throws IOException {
		String source_X = 
			"public class X {\n" +
			"  //@ invariant 3; // error\n" + 
			"  public void m() {}\n" + 
			"}\n";
		String xPath = "X.java";
		String[] pathAndContents = new String[] {
				xPath,
				source_X
		};
		JmlCoreTestsUtil.createSourceDir(pathAndContents, SOURCE_DIRECTORY);
		String srcPath = ""; // must be blank for bug to show, otherwise
		String destDir = SOURCE_DIRECTORY; // use source as destination for .class files.
		String result;
		String expected = "----------\n"+
						"1. ERROR in "+ destDir + File.separator + xPath+" (at line 2)\n"+
						"	//@ invariant 3; // error\n"+
						"  public void m() {}\n"+
						"	^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"+
						"JML Checker: A boolean valued expression is required in this context [JML]\n"+
						"----------\n"+
						"1 problem (1 error)";
		System.setProperty("jdt.compiler.useSingleThread", "true");
    	String batchCompilerOptions = "-jml2";
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + xPath, srcPath, destDir);
		assertEquals(xPath + ": " + result, expected, result); 
	}

	public void _test_0003_JML2Sanity() throws IOException {
		String source_X = 
			"public class X {\n" +
			"  //@ invariant true;\n" + 
			"  public void m() {}\n" + 
			"}\n";
		String xPath = "X.java";
		String[] pathAndContents = new String[] {
				xPath,
				source_X
		};
		JmlCoreTestsUtil.createSourceDir(pathAndContents, SOURCE_DIRECTORY);
		String srcPath = ""; // must be blank for bug to show, otherwise
		String destDir = SOURCE_DIRECTORY; // use source as destination for .class files.
		String result;
		String expected = "";
		System.setProperty("jdt.compiler.useSingleThread", "true");
    	String batchCompilerOptions = "-jml2c";
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + xPath, srcPath, destDir);
		assertEquals(xPath + ": " + result, expected, result); 
	}

	public void _test_0004_JML2Sanity() throws IOException {
		String source_X = 
			"public class X {\n" +
			"  //@ invariant 3; // error\n" + 
			"  public void m() {}\n" + 
			"}\n";
		String xPath = "X.java";
		String[] pathAndContents = new String[] {
				xPath,
				source_X
		};
		JmlCoreTestsUtil.createSourceDir(pathAndContents, SOURCE_DIRECTORY);
		String srcPath = ""; // must be blank for bug to show, otherwise
		String destDir = SOURCE_DIRECTORY; // use source as destination for .class files.
		String result;
		String expected = "----------\n"+
						"1. WARNING in " + destDir + File.separator + xPath + " (at line 1)\n"+
						"	public class X {\n"+
						"	^\n"+
						"warning: Ignoring command-line argument that does not exist - \"" + destDir + File.separator + xPath + "\" [MJC]\n"+
						"----------\n"+
						"1 problem (1 warning)";
		System.setProperty("jdt.compiler.useSingleThread", "true");
    	String batchCompilerOptions = "-jml2c";
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + xPath, srcPath, destDir);
		assertEquals(xPath + ": " + result, expected, result); 
	}

}
