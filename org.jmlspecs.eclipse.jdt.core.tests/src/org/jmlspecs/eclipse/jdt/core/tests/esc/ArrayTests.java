package org.jmlspecs.eclipse.jdt.core.tests.esc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.PostProcessor;

public class ArrayTests extends AbstractRegressionTest {
	public ArrayTests(String name) {
		super(name);
	}

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		PostProcessor.useOldErrorReporting = true;
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		PostProcessor.useOldErrorReporting = false;
	}

	// Augment problem detection settings
	@Override
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
		Map<String, String> options = super.getCompilerOptions();

		options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
		options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
		options.put(JmlCompilerOptions.OPTION_EnableJmlEsc, CompilerOptions.ENABLED);
		options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NON_NULL);
		options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.ERROR);
		options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.ERROR);
		options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.ERROR);
		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
		// options.put(JmlCompilerOptions.OPTION_SpecPath,
		// NullTypeSystemTestCompiler.getSpecPath());
		options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_Source, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_TargetPlatform, CompilerOptions.VERSION_1_5);
		return options;
	}

//	private final String testsPath = "tests" + File.separatorChar + "esc" + File.separatorChar;
	// the line above fails under linux.  the following works under both linux & cygwin.
	private final String testsPath = "tests" + '\\' + "esc" + '\\';

	public void test_0001_readArray() {
		this.runNegativeTest(new String[] {
				testsPath + "Array_0001.java",
				"package tests.esc;\n" +
				"public class Array_0001 {\n" +
				"   //@ requires n.length >= 4;\n" + 
				"   //@ ensures  \\result == n[3];\n" + 
				"   public int m1(int[] n) {\n" + 
				"      return n[3];\n" + 
				"   }\n" + 
				"}\n"
				},
				"");
	}

	public void test_0002_oldArrayRead() {
		this.runNegativeTest(new String[] {
				testsPath + "Array_0002.java",
				"package tests.esc;\n" +
				"public class Array_0002 {\n" +
				"   //@ ensures \\result == \\old(n[2]) + 1;\n" + 
				"   public int m1(int[] n) {\n" + 
				"      int result = n[2] + 1;\n" + 
				"      n[2] = 42;\n" + 
				"      return result;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0003_writeArray() {
		this.runNegativeTest(new String[] {
				testsPath + "Array_0003.java",
				"package tests.esc;\n" +
				"public class Array_0003 {\n" +
				"   //@ ensures \\result == 42;\n" + 
				"   public int m1(int[] n) {\n" + 
				"      n[2] = 42;\n" + 
				"      return n[2];\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0004_postfixArray() {
		this.runNegativeTest(new String[] {
				testsPath + "Array_0004.java",
				"package tests.esc;\n" +
				"public class Array_0004 {\n" +
				"   //@ ensures n[2] == 42 && \\result == 41;\n" + 
				"   public int m1(int[] n) {\n" + 
				"      n[2] = 41;\n" + 
				"      return n[2]++;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0005_compoundAssignment() {
		this.runNegativeTest(new String[] {
				testsPath + "Array_0005.java",
				"package tests.esc;\n" +
				"public class Array_0005 {\n" +
				"   //@ ensures n[2] == \\old(n[2]) + 1;\n" + 
				"   public void m1(int[] n) {\n" + 
				"      n[2] += 1;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0006_arrayLength() {
		this.runNegativeTest(new String[] {
				testsPath + "Array_0006.java",
				"package tests.esc;\n" +
				"public class Array_0006 {\n" +
				"   //@ requires n.length >= 4;\n" + 
				"   //@ ensures  \\result == n[3];\n" + 
				"   public int m1(int[] n) {\n" + 
				"      return n[3];\n" + 
				"   }\n" + 
				"   public int m2(int[] m) {\n" + 
				"      return m1(m);\n" + 
				"   }\n" + 
				"}\n" 
				},
				"----------\n" + 
				"1. ERROR in tests\\esc\\Array_0006.java (at line 3)\n" + 
				"	//@ requires n.length >= 4;\n" + 
				"	             ^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Precondition).\n" + 
				"----------\n");
	}

	public void test_0007_arrayLengthNonNeg() {
		this.runNegativeTest(new String[] {
				testsPath + "Array_0007.java",
				"package tests.esc;\n" +
				"public class Array_0007 {\n" +
				"   public void m1(int[] n) {\n" + 
				"      assert n.length >= 0;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}
	public void _test_0010_returnArray() {
		this.runNegativeTest(new String[] {
				testsPath + "Array_0010.java",
				"package tests.esc;\n" +
				"public class Array_0010 {\n" +
				"   //@ ensures \\result[2] == 42;\n" + 
				"   public int[] m10(int[] n) {\n" + 
				"      n[2] = 42;\n" + 
				"      return n;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

}