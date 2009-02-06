package org.jmlspecs.eclipse.jdt.core.tests.esc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class FieldTests extends AbstractRegressionTest {
	public FieldTests(String name) {
		super(name);
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
		options.put(CompilerOptions.OPTION_ReportNonStaticAccessToStatic, CompilerOptions.IGNORE);
		return options;
	}

//	private final String testsPath = "tests" + File.separatorChar + "esc" + File.separatorChar;
	// the line above fails under linux.  the following works under both linux & cygwin.
	private final String testsPath = "tests" + '\\' + "esc" + '\\';

	public void test_0001_readField() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0001.java",
				"package tests.esc;\n" +
				"public class Field_0001 {\n" +
				"   public int n;\n" + 
				"   //@ ensures \\result == n + 1;\n" + 
				"   public int m1() {\n" + 
				"      return n+1;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0002_oldFieldRead() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0002.java",
				"package tests.esc;\n" +
				"public class Field_0002 {\n" +
				"   public int n;\n" + 
				"   //@ ensures \\result == \\old(n) + 1;\n" + 
				"   public int m1() {\n" + 
				"      return n+1;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0003_writeField() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0003.java",
				"package tests.esc;\n" +
				"public class Field_0003 {\n" +
				"   public int n;\n" + 
				"   //@ ensures n == \\old(n) + 1;\n" + 
				"   public void m1() {\n" + 
				"      n = n + 1;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0004_postfixField() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0004.java",
				"package tests.esc;\n" +
				"public class Field_0004 {\n" +
				"   public int n;\n" + 
				"   //@ ensures n == \\old(n) + 1;\n" + 
				"   //@ ensures \\result == n - 1;\n" + 
				"   public int m1() {\n" + 
				"      return n++;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0005_compoundAssignment() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0005.java",
				"package tests.esc;\n" +
				"public class Field_0005 {\n" +
				"   public int n;\n" + 
				"   //@ ensures n == \\old(n) + 1;\n" + 
				"   public void m1() {\n" + 
				"      n += 1;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0006_staticFieldInPost() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0001.java",
				"package tests.esc;\n" +
				"public class Field_0001 {\n" +
				"   public static int n;\n" + 
				"   //@ ensures n == \\old(n) + 1;\n" + 
				"   public void m1() {\n" + 
				"      n++;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}
	
	public void test_0007_thisExpressioin() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0001.java",
				"package tests.esc;\n" +
				"public class Field_0001 {\n" +
				"   public int n;\n" + 
				"   //@ ensures n == \\old(n) + 1;\n" + 
				"   public void m1() {\n" + 
				"      this.n++;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0008_qualWriteField() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0003.java",
				"package tests.esc;\n" +
				"public class Field_0003 {\n" +
				"   public int n;\n" + 
				"   //@ ensures x.n == \\old(this.n) + 1;\n" + 
				"   public void m1(Field_0003 x) {\n" + 
				"      x.n = this.n + 1;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0009_thisStatic() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0003.java",
				"package tests.esc;\n" +
				"public class Field_0003 {\n" +
				"   public static int n;\n" + 
				"   //@ ensures x.n == \\old(this.n) + 1;\n" + 
				"   public void m1(Field_0003 x) {\n" + 
				"      x.n = this.n + 1;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}

	public void test_0010_anotherStatic() {
		this.runNegativeTest(new String[] {
				testsPath + "Field_0003.java",
				"package tests.esc;\n" +
				"public class Field_0003 {\n" +
				"   public static int n;\n" + 
				"   //@ ensures n == \\old(n) + 1;\n" + 
				"   public void m1(Field_0003 x) {\n" + 
				"      x.n = this.n + 1;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}
}