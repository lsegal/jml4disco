package org.jmlspecs.eclipse.jdt.core.tests.esc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.PostProcessor;

public class InitialTests extends AbstractRegressionTest {
	public InitialTests(String name) {
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
	
	public void test_001_assertFalse() {
		this.runNegativeTest(new String[] {
				testsPath + "A.java",
				"package tests.esc;\n" +
				"public class A {\n" +
				"   public void m() {\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + "}\n" 
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "A.java (at line 4)\n" + 
				"	//@ assert false;\n" +
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}

	public void test_002_assertTrue() {
		this.runNegativeTest(new String[] {
				testsPath + "B.java",
				"package tests.esc;\n" +
				"public class B {\n" + 
				"   public void m() {\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"");
	}

	public void test_003_assumeFalse() {
		this.runNegativeTest(new String[] {
				testsPath + "C.java",
				"package tests.esc;\n" +
				"public class C {\n" + 
				"   public void m() {\n" + 
				"      //@ assume false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"");
	}

	public void test_004_assumeTrue() {
		this.runNegativeTest(new String[] {
				testsPath + "D.java",
				"package tests.esc;\n" +
				"public class D {\n" + 
				"   public void m() {\n" + 
				"      //@ assume true;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"");
	}

	public void test_005_assertParam() {
		this.runNegativeTest(new String[] {
				testsPath + "E.java",
				"package tests.esc;\n" +
				"public class E {\n" + 
				"   public void m(boolean b) {\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "E.java (at line 4)\n" + 
				"	//@ assert b;\n" +
				"	           ^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}

	public void test_010_sequence_tt() {
		this.runNegativeTest(new String[] {
				testsPath + "F.java",
				"package tests.esc;\n" +
				"public class F {\n" + 
				"   public void m() {\n" + 
				"      //@ assume true;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"");
	}
	public void test_011_sequence_tf() {
		this.runNegativeTest(new String[] {
				testsPath + "G.java",
				"package tests.esc;\n" +
				"public class G {\n" + 
				"   public void m() {\n" + 
				"      //@ assume true;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "G.java (at line 5)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_012_sequence_ft() {
		this.runNegativeTest(new String[] {
				testsPath + "H.java",
				"package tests.esc;\n" +
				"public class H {\n" + 
				"   public void m() {\n" + 
				"      //@ assume false;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"");
	}
	public void test_013_sequence_ff() {
		this.runNegativeTest(new String[] {
				testsPath + "I.java",
				"package tests.esc;\n" +
				"public class I {\n" + 
				"   public void m() {\n" + 
				"      //@ assume false;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"");
	}
	public void test_014_sequence_ff() {
		this.runNegativeTest(new String[] {
				testsPath + "J.java",
				"package tests.esc;\n" +
				"public class J {\n" + 
				"   public void m() {\n" + 
				"      //@ assert false;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "J.java (at line 4)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_015_sequence_and() {
		this.runNegativeTest(new String[] {
				testsPath + "K.java",
				"package tests.esc;\n" +
				"public class K {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert false && false;\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert false & false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "K.java (at line 4)\n" + 
				"	//@ assert false && false;\n" +
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "K.java (at line 7)\n" + 
				"	//@ assert false & false;\n" +
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_016_sequence_or() {
		this.runNegativeTest(new String[] {
				testsPath + "L.java",
				"package tests.esc;\n" +
				"public class L {\n" + 
				"   public void m() {\n" + 
				"      //@ assert false || false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "L.java (at line 4)\n" + 
				"	//@ assert false || false;\n" + 
				"	           ^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_017_sequence_and_or() {
		this.runNegativeTest(new String[] {
				testsPath + "M.java",
				"package tests.esc;\n" +
				"public class M {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert false && (false || false);\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert false & (false | false);\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in tests\\esc\\M.java (at line 4)\n" + 
				"	//@ assert false && (false || false);\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in tests\\esc\\M.java (at line 7)\n" + 
				"	//@ assert false & (false | false);\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in tests\\esc\\M.java (at line 7)\n" + 
				"	//@ assert false & (false | false);\n" + 
				"	                   ^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_018_sequence_or_and() {
		this.runNegativeTest(new String[] {
				testsPath + "N.java",
				"package tests.esc;\n" +
				"public class N {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert (false | false) & false;\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert (false || false) && false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in tests\\esc\\N.java (at line 4)\n" + 
				"	//@ assert (false | false) & false;\n" + 
				"	           ^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in tests\\esc\\N.java (at line 4)\n" + 
				"	//@ assert (false | false) & false;\n" + 
				"	                             ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in tests\\esc\\N.java (at line 7)\n" + 
				"	//@ assert (false || false) && false;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_019_conditional() {
		this.runNegativeTest(new String[] {
				testsPath + "O.java",
				"package tests.esc;\n" +
				"public class O {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert (true ? true : true);\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert (true ? true : false);\n" + 
				"   }\n" + 
				"   public void m3() {\n" + 
				"      //@ assert (true ? false : true);\n" + 
				"   }\n" + 
				"   public void m4() {\n" + 
				"      //@ assert (true ? false : false);\n" + 
				"   }\n" + 
				"   public void m5() {\n" + 
				"      //@ assert (false ? true : true);\n" + 
				"   }\n" + 
				"   public void m6() {\n" + 
				"      //@ assert (false ? true : false);\n" + 
				"   }\n" + 
				"   public void m7() {\n" + 
				"      //@ assert (false ? false : true);\n" + 
				"   }\n" + 
				"   public void m8() {\n" + 
				"      //@ assert (false ? false : false);\n" + 
				"   }\n" + 
				"   public void m9() {\n" + 
				"      //@ assert (false ? false : \n" +
				"                          (false ? false : true));\n" + 
				"   }\n" + 
				"   public void m10() {\n" + 
				"      //@ assert (false ? false : \n" +
				"                          (false ? false : false));\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in tests\\esc\\O.java (at line 10)\n" + 
				"	//@ assert (true ? false : true);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in tests\\esc\\O.java (at line 13)\n" + 
				"	//@ assert (true ? false : false);\n" + 
				"	                   ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in tests\\esc\\O.java (at line 19)\n" + 
				"	//@ assert (false ? true : false);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"4. ERROR in tests\\esc\\O.java (at line 25)\n" + 
				"	//@ assert (false ? false : false);\n" + 
				"	            ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"5. ERROR in tests\\esc\\O.java (at line 32)\n" + 
				"	//@ assert (false ? false : \n" + 
				"                          (false ? false : false));\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_020_int_eq() {
		this.runNegativeTest(new String[] {
				testsPath + "P.java",
				"package tests.esc;\n" +
				"public class P {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert 42 == 42;\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert 42 == 43;\n" + 
				"   }\n" + 
				"   public void m3() {\n" + 
				"      //@ assert 42 != 42;\n" + 
				"   }\n" + 
				"   public void m4() {\n" + 
				"      //@ assert 42 != 43;\n" + 
				"   }\n" + 
				"   public void m5() {\n" + 
				"      //@ assert 42 < 42;\n" + 
				"   }\n" + 
				"   public void m6() {\n" + 
				"      //@ assert 42 < 43;\n" + 
				"   }\n" + 
				"   public void m7() {\n" + 
				"      //@ assert 42 > 42;\n" + 
				"   }\n" + 
				"   public void m8() {\n" + 
				"      //@ assert 42 > 43;\n" + 
				"   }\n" + 
				"   public void m9() {\n" + 
				"      //@ assert 43 <= 42;\n" + 
				"   }\n" + 
				"   public void m10() {\n" + 
				"      //@ assert 42 <= 42;\n" + 
				"   }\n" + 
				"   public void m11() {\n" + 
				"      //@ assert 42 <= 43;\n" + 
				"   }\n" + 
				"   public void m12() {\n" + 
				"      //@ assert 42 >= 43;\n" + 
				"   }\n" + 
				"   public void m13() {\n" + 
				"      //@ assert 42 >= 42;\n" + 
				"   }\n" + 
				"   public void m14() {\n" + 
				"      //@ assert 43 >= 42;\n" + 
				"   }\n" + 
				"   public void m15() {\n" + 
				"      //@ assert (42 >= 42) == true;\n" + 
				"   }\n" + 
				"   public void m16() {\n" + 
				"      //@ assert (42 >= 42) == false;\n" + 
				"   }\n" + 
				"   public void m17() {\n" + 
				"      //@ assert (43 >= 42) == true;\n" + 
				"   }\n" + 
				"   public void m18() {\n" + 
				"      //@ assert (43 >= 42) == false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "P.java (at line 7)\n" + 
				"	//@ assert 42 == 43;\n" + 
				"	           ^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "P.java (at line 10)\n" + 
				"	//@ assert 42 != 42;\n" + 
				"	           ^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in " + testsPath + "P.java (at line 16)\n" + 
				"	//@ assert 42 < 42;\n" + 
				"	           ^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"4. ERROR in " + testsPath + "P.java (at line 22)\n" + 
				"	//@ assert 42 > 42;\n" + 
				"	           ^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"5. ERROR in " + testsPath + "P.java (at line 25)\n" + 
				"	//@ assert 42 > 43;\n" + 
				"	           ^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"6. ERROR in " + testsPath + "P.java (at line 28)\n" + 
				"	//@ assert 43 <= 42;\n" + 
				"	           ^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"7. ERROR in " + testsPath + "P.java (at line 37)\n" + 
				"	//@ assert 42 >= 43;\n" + 
				"	           ^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"8. ERROR in " + testsPath + "P.java (at line 49)\n" + 
				"	//@ assert (42 >= 42) == false;\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"9. ERROR in " + testsPath + "P.java (at line 55)\n" + 
				"	//@ assert (43 >= 42) == false;\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_021_int_arith() {
		this.runNegativeTest(new String[] {
				testsPath + "R.java",
				"package tests.esc;\n" +
				"public class R {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert 5 + 2 == 7;\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert 5 - 2 == 3;\n" + 
				"   }\n" + 
				"   public void m3() {\n" + 
				"      //@ assert 5 * 2 == 10;\n" + 
				"   }\n" + 
				"   public void m4() {\n" + 
				"      //@ assert 4 / 2 == 2;\n" + 
				"   }\n" + 
				"   public void m5() {\n" + 
				"      //@ assert 5 % 2 == 1;\n" + 
				"   }\n" + 
				"   public void m1b() {\n" + 
				"      //@ assert 5 + 2 != 7;\n" + 
				"   }\n" + 
				"   public void m2b() {\n" + 
				"      //@ assert 5 - 2 != 3;\n" + 
				"   }\n" + 
				"   public void m3b() {\n" + 
				"      //@ assert 5 * 2 != 10;\n" + 
				"   }\n" + 
				"   public void m4b() {\n" + 
				"      //@ assert 4 / 2 != 2;\n" + 
				"   }\n" + 
				"   public void m5b() {\n" + 
				"      //@ assert 5 % 2 != 1;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "R.java (at line 19)\n" + 
				"	//@ assert 5 + 2 != 7;\n" + 
				"	           ^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "R.java (at line 22)\n" + 
				"	//@ assert 5 - 2 != 3;\n" + 
				"	           ^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in " + testsPath + "R.java (at line 25)\n" + 
				"	//@ assert 5 * 2 != 10;\n" + 
				"	           ^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"4. ERROR in " + testsPath + "R.java (at line 28)\n" + 
				"	//@ assert 4 / 2 != 2;\n" + 
				"	           ^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"5. ERROR in " + testsPath + "R.java (at line 31)\n" + 
				"	//@ assert 5 % 2 != 1;\n" + 
				"	           ^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_022_arith_cond() {
		this.runNegativeTest(new String[] {
				testsPath + "S.java",
				"package tests.esc;\n" +
				"public class S {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert (5 == 3 + 2 ? 42 == 6 * 7 : 1 + 1 == 2);\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert (5 == 3 + 2 ? 42 > 6 * 7 : 1 + 1 == 2);\n" + 
				"   }\n" + 
				"   public void m3() {\n" + 
				"      //@ assert (5 == 3 + 3 ? 42 == 6 * 7 : 1 + 1 != 2);\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "S.java (at line 7)\n" + 
				"	//@ assert (5 == 3 + 2 ? 42 > 6 * 7 : 1 + 1 == 2);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "S.java (at line 10)\n" + 
				"	//@ assert (5 == 3 + 3 ? 42 == 6 * 7 : 1 + 1 != 2);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_023_boolExpr_cond() {
		this.runNegativeTest(new String[] {
				testsPath + "T.java",
				"package tests.esc;\n" +
				"public class T {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert (!true ? false : !true);\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert (false && false ? true : false && false);\n" + 
				"   }\n" + 
				"   public void m3() {\n" + 
				"      //@ assert (false || false ? true : false || false);\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "T.java (at line 4)\n" + 
				"	//@ assert (!true ? false : !true);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "T.java (at line 7)\n" + 
				"	//@ assert (false && false ? true : false && false);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in " + testsPath + "T.java (at line 10)\n" + 
				"	//@ assert (false || false ? true : false || false);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_035_implies() {
		this.runNegativeTest(new String[] {
				testsPath + "U.java",
				"package tests.esc;\n" +
				"public class U {\n" + 
				"   public void m1() {\n" +
				"      //@ assert (true ==> true);\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert (true ==> false);\n" + 
				"   }\n" + 
				"   public void m3() {\n" + 
				"      //@ assert (false ==> true);\n" + 
				"   }\n" + 
				"   public void m4() {\n" + 
				"      //@ assert (false ==> false);\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "U.java (at line 7)\n" + 
				"	//@ assert (true ==> false);\n" + 
				"	                     ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_036_rev_implies() {
		this.runNegativeTest(new String[] {
				testsPath + "V.java",
				"package tests.esc;\n" +
				"public class V {\n" + 
				"   public void m1() {\n" +
				"      //@ assert (true <== true);\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert (true <== false);\n" + 
				"   }\n" + 
				"   public void m3() {\n" + 
				"      //@ assert (false <== true);\n" + 
				"   }\n" + 
				"   public void m4() {\n" + 
				"      //@ assert (false <== false);\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "V.java (at line 10)\n" + 
				"	//@ assert (false <== true);\n" + 
				"	            ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_037_equiv() {
		this.runNegativeTest(new String[] {
				testsPath + "W.java",
				"package tests.esc;\n" +
				"public class W {\n" + 
				"   public void m1() {\n" +
				"      //@ assert (true <==> true);\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert (true <==> false);\n" + 
				"   }\n" + 
				"   public void m3() {\n" + 
				"      //@ assert (false <==> true);\n" + 
				"   }\n" + 
				"   public void m4() {\n" + 
				"      //@ assert (false <==> false);\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "W.java (at line 7)\n" + 
				"	//@ assert (true <==> false);\n" + 
				"	           ^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "W.java (at line 10)\n" + 
				"	//@ assert (false <==> true);\n" + 
				"	           ^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_038_not_equiv() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m1() {\n" +
				"      //@ assert (true <=!=> true);\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert (true <=!=> false);\n" + 
				"   }\n" + 
				"   public void m3() {\n" + 
				"      //@ assert (false <=!=> true);\n" + 
				"   }\n" + 
				"   public void m4() {\n" + 
				"      //@ assert (false <=!=> false);\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "X.java (at line 4)\n" + 
				"	//@ assert (true <=!=> true);\n" + 
				"	           ^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "X.java (at line 13)\n" + 
				"	//@ assert (false <=!=> false);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_050_twoMethods() {
		this.runNegativeTest(new String[] {
				testsPath + "Y.java",
				"package tests.esc;\n" +
				"public class Y {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m2() {\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "Y.java (at line 4)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" +
				"2. ERROR in " + testsPath + "Y.java (at line 7)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_100_method_param() {
		this.runNegativeTest(new String[] {
				testsPath + "Z.java",
				"package tests.esc;\n" +
				"public class Z {\n" + 
				"   public void m1(boolean b) {\n" + 
				"      //@ assume b;\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 
				"   public void m2(boolean b) {\n" +
				"      //@ assume  b;\n" +
				"      //@ assert !b;\n" +
				"   }\n" +
				"   public void m3(int n) {\n" +
				"      //@ assume n==3;\n" +
				"      //@ assert n<4;\n" +
				"   }\n" +
				"   public void m4(int n) {\n" +
				"      //@ assume n==3;\n" +
				"      //@ assert n<0;\n" +
				"   }\n" +
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "Z.java (at line 9)\n" + 
				"	//@ assert !b;\n" + 
				"	           ^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "Z.java (at line 17)\n" + 
				"	//@ assert n<0;\n" + 
				"	           ^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_101_localVarDecls() {
		this.runNegativeTest(new String[] {
				testsPath + "AA.java",
				"package tests.esc;\n" +
				"public class AA {\n" + 
				"   public void m1() {\n" + 
				"      boolean b = true;\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 
				"   public void m2() {\n" +
				"      boolean b = true;\n" + 
				"      //@ assert !b;\n" +
				"   }\n" +
				"   public void m3() {\n" +
				"      int n=3;\n" +
				"      //@ assert n<4;\n" +
				"   }\n" +
				"   public void m4() {\n" +
				"      int n=3;\n" +
				"      //@ assert n<0;\n" +
				"   }\n" +
				"   public void m5() {\n" +
				"       { int n=3;\n" +
				"         //@ assert n==3;\n" +
				"       }\n" +
				"       { int n=4;\n" +
				"         //@ assert n!=3;\n" +
				"       }\n" +
				"   }\n" +
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "AA.java (at line 9)\n" + 
				"	//@ assert !b;\n" + 
				"	           ^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "AA.java (at line 17)\n" + 
				"	//@ assert n<0;\n" + 
				"	           ^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_150_if() {
		this.runNegativeTest(new String[] {
				testsPath + "AB.java",
				"package tests.esc;\n" +
				"public class AB {\n" + 
				"   public void m1(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"   }\n" + 
				"   public void m2(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a <= 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"   }\n" + 
				"   public void m3(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a >= 0;\n" + 
				"      }\n" + 
				"   }\n" + 
				"   public void m4(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"   public void m5(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"   public void m6() {\n" + 
				"      if (true) {\n" + 
				"         //@ assert false;\n" + 
				"      } else {\n" +
				"         //@ assert true;\n" + 
				"      }\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"   public void m7() {\n" + 
				"      if (true) {\n" + 
				"         //@ assert true;\n" + 
				"      } else {\n" +
				"         //@ assert true;\n" + 
				"      }\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m8(int i) {\n" + 
				"      int r;\n" + 
				"      if (i < 0) {\n" + 
				"         r = -i;\n" + 
				"      } else {\n" +
				"         r = i;\n" + 
				"      }\n" + 
				"      //@ assert r < 0;\n" + 
				"   }\n" + 
				"   public void m9(int i) {\n" + 
				"      int r;\n" + 
				"      if (i < 0) {\n" + 
				"         r = -i;\n" + 
				"      } else {\n" +
				"         r = i;\n" + 
				"      }\n" + 
				"      //@ assert r >= 0;\n" + 
				"   }\n" + 
				"   public void m10(int i) {\n" + 
				"      if (i < 0) {\n" + 
				"         i = -i;\n" + 
				"      }\n" + 
				"      //@ assert i < 0;\n" + 
				"   }\n" + 
				"   public void m11(int i) {\n" + 
				"      if (i < 0) {\n" + 
				"         i = -i;\n" + 
				"      }\n" + 
				"      //@ assert i >= 0; // 88\n" + 
				"   }\n" + 
				"   public void m12() {\n" + 
				"      if (true) {\n" + 
				"      	  //@ assert false;\n" + 
				"      }\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "AB.java (at line 14)\n" + 
				"	//@ assert a <= 0;\n" + 
				"	           ^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "AB.java (at line 24)\n" + 
				"	//@ assert a >= 0;\n" + 
				"	           ^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in " + testsPath + "AB.java (at line 47)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"4. ERROR in " + testsPath + "AB.java (at line 59)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"5. ERROR in " + testsPath + "AB.java (at line 68)\n" +
				"	//@ assert r < 0;\n" +
				"	           ^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n" + 
				"6. ERROR in " + testsPath + "AB.java (at line 83)\n" +
				"	//@ assert i < 0;\n" +
				"	           ^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n" +
				"7. ERROR in " + testsPath + "AB.java (at line 93)\n" +
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_151_if_condWithSideEffects() {
		this.runNegativeTest(new String[] {
				testsPath + "AC.java",
				"package tests.esc;\n" +
				"public class AC {\n" + 
				"   public void m1(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (++a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m2(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a++ > 0) {\n" + 
				"         //@ assert a > 1;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 1;\n" + 
				"      }\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m3(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if ((a+=5) > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "AC.java (at line 10)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "AC.java (at line 19)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in " + testsPath + "AC.java (at line 28)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_0155_if_noAfter() {
		this.runNegativeTest(new String[] {
				testsPath + "INA.java",
				"package tests.esc;\n" +
				"public class INA {\n" + 
				"   public static int m(int a, int b) {\n" +
				"		if (b == 0)\n"+
				"          return a;\n" +
				"		else {\n"+
				"          return b;\n" +
				"       }\n" +
				"    }\n" +
				"}\n" 
				}, 
				"");
	}

	public void test_0200_assignment() {
		this.runNegativeTest(new String[] {
				testsPath + "AD.java",
				"package tests.esc;\n" +
				"public class AD {\n" + 
				"   public void m1(boolean b) {\n" + 
				"      b = true;\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 
				"   public void m2(boolean b) {\n" + 
				"      b = true;\n" + 
				"      //@ assert !b;\n" + 
				"   }\n" + 
				"   public void m3(int a, int b) {\n" + 
				"      a = 3 + (b=2);\n" + 
				"      //@ assert a == 5 && b == 2;\n" + 
				"   }\n" + 
				"   public void m4(int a, int b) {\n" + 
				"      a = 3 + (b=2);\n" + 
				"      //@ assert a != 5 || b != 2;\n" + 
				"   }\n" + 
				"   public void m5(int a, int b) {\n" + 
				"      b = 1;\n" + 
				"      a = b + (b=2) + b + (b=3) + b;\n" + 
				"      //@ assert a == 11 && b == 3;\n" + 
				"   }\n" + 
				"   public void m6(int a, int b) {\n" + 
				"      b = 1;\n" + 
				"      a = b + (b=2) + b + (b=3) + b;\n" + 
				"      //@ assert a != 11 || b != 3;\n" + 
				"   }\n" + 
				"   public void m7(int a, int b) {\n" + 
				"      a = 1;\n" + 
				"      b = 2;\n" + 
				"      a = 3;\n" + 
				"      //@ assert a != 3 || b != 2;\n" + 
				"   }\n" + 
				"   public void m8(int a, int b) {\n" + 
				"      a = 1;\n" + 
				"      b = 2;\n" + 
				"      a += b;\n" + 
				"      //@ assert a != 3 || b != 2;\n" + 
				"   }\n" + 
				"   public void m9(int a, int b) {\n" + 
				"      a = 1;\n" + 
				"      b = 2;\n" + 
				"      a -= b;\n" + 
				"      //@ assert a != -1 || b != 2;\n" + 
				"   }\n" + 
				"   public void m10(int a, int b) {\n" + 
				"      a = 3;\n" + 
				"      b = 2;\n" + 
				"      a *= b;\n" + 
				"      //@ assert a != 6 || b != 2;\n" + 
				"   }\n" + 
				"   public void m11(int a, int b) {\n" + 
				"      a = 6;\n" + 
				"      b = 2;\n" + 
				"      a /= b;\n" + 
				"      //@ assert a != 3 || b != 2;\n" + 
				"   }\n" + 
				"   public void m12(int a, int b) {\n" + 
				"      a = 5;\n" + 
				"      b = 2;\n" + 
				"      a = b++;\n" + 
				"      //@ assert a != 2 || b != 3;\n" + 
				"   }\n" + 
				"   public void m13(int a, int b) {\n" + 
				"      a = 5;\n" + 
				"      b = 2;\n" + 
				"      a = ++b;\n" + 
				"      //@ assert a != 3 || b != 3;\n" + 
				"   }\n" + 
				"   public void m14(int a, int b) {\n" + 
				"      a = 5;\n" + 
				"      b = 2;\n" + 
				"      a = b--;\n" + 
				"      //@ assert a != 2 || b != 1;\n" + 
				"   }\n" + 
				"   public void m15(int a, int b) {\n" + 
				"      a = 5;\n" + 
				"      b = 2;\n" + 
				"      a = --b;\n" + 
				"      //@ assert a != 1 || b != 1;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"----------\n" + 
				"1. ERROR in " + testsPath + "AD.java (at line 9)\n" + 
				"	//@ assert !b;\n" + 
				"	           ^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "AD.java (at line 17)\n" + 
				"	//@ assert a != 5 || b != 2;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in " + testsPath + "AD.java (at line 27)\n" + 
				"	//@ assert a != 11 || b != 3;\n" + 
				"	           ^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"4. ERROR in " + testsPath + "AD.java (at line 33)\n" + 
				"	//@ assert a != 3 || b != 2;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"5. ERROR in " + testsPath + "AD.java (at line 39)\n" + 
				"	//@ assert a != 3 || b != 2;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"6. ERROR in " + testsPath + "AD.java (at line 45)\n" + 
				"	//@ assert a != -1 || b != 2;\n" + 
				"	           ^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"7. ERROR in " + testsPath + "AD.java (at line 51)\n" + 
				"	//@ assert a != 6 || b != 2;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"8. ERROR in " + testsPath + "AD.java (at line 57)\n" + 
				"	//@ assert a != 3 || b != 2;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"9. ERROR in " + testsPath + "AD.java (at line 63)\n" + 
				"	//@ assert a != 2 || b != 3;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"10. ERROR in " + testsPath + "AD.java (at line 69)\n" + 
				"	//@ assert a != 3 || b != 3;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"11. ERROR in " + testsPath + "AD.java (at line 75)\n" + 
				"	//@ assert a != 2 || b != 1;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"12. ERROR in " + testsPath + "AD.java (at line 81)\n" + 
				"	//@ assert a != 1 || b != 1;\n" + 
				"	           ^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_0300_lightweightContracts() {
		this.runNegativeTest(new String[] {
				testsPath + "LWMC.java",
				"package tests.esc;\n" +
				"public class LWMC {\n" + 
				"   //@ requires i > 10;\n" +
				"   //@ ensures \\result < -10;\n" +
				"   public static int m1(int i) {\n" +
				"	   //@ return -i;\n" +
				"	}\n" +
				"   //@ requires i < 10;\n" +
				"   //@ ensures \\result < -10;\n" +
				"   public static int m2(int i) {\n" +
				"	   //@ return -i;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "LWMC.java (at line 9)\n" + 
				"	//@ ensures \\result < -10;\n" +
				"	            ^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Postcondition).\n" + 
				"----------\n");
	}
	public void test_0350_methodCalls() {
		this.runNegativeTest(new String[] {
				testsPath + "PMC.java",
				"package tests.esc;\n" +
				"public class PMC {\n" + 
				"   //@ requires i > 0;\n" +
				"   //@ ensures \\result == i * i + 1;\n" +
				"   public static int sq_p1(int i) {\n" +
				"	   return i*i + 1;\n" +
				"	}\n" +
				"   public static void m1() {\n" +
				"	   //@ assert 26 == sq_p1(5);\n" +
				"	   int n = 5;\n" +
				"	   //@ assert 26 == sq_p1(n);\n" +
				"	}\n" +
				"   public static void m2() {\n" +
				"	   //@ assert 37 != sq_p1(6);\n" +
				"	   int n = 6;\n" +
				"	   //@ assert 37 != sq_p1(n);\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "PMC.java (at line 14)\n" + 
				"	//@ assert 37 != sq_p1(6);\n" +
				"	           ^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "PMC.java (at line 16)\n" + 
				"	//@ assert 37 != sq_p1(n);\n" +
				"	           ^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_0355_methodCallsInSpecs() {
		this.runNegativeTest(new String[] {
				testsPath + "MCIS1.java",
				"package tests.esc;\n" +
				"public class MCIS1 {\n" + 
				"   //@ requires i > 0;\n" +
				"   //@ ensures \\result == i * i;\n" +
				"   public static int sq(int i) {\n" +
				"	   return i*i;\n" +
				"	}\n" +
				"   //@ requires i > 0;\n" +
				"   //@ ensures \\result == i * sq(i);\n" +
				"   public static int cube(int i) {\n" +
				"	   return i*i*i;\n" +
				"	}\n" +
				"   //@ requires i > 1;\n" +
				"   public static void m1(int i) {\n" +
				"	   //@ assert cube(i) == i * i * i;\n" +
				"	}\n" +
				"   //@ requires i > 1;\n" +
				"   public static void m2(int i) {\n" +
				"	   //@ assert cube(i) == i * i + i;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "MCIS1.java (at line 19)\n" + 
				"	//@ assert cube(i) == i * i + i;\n" +
				"	           ^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	public void test_0356_methodCallsInQuantifiers() {
		this.runNegativeTest(new String[] {
				testsPath + "MCIS2.java",
				"package tests.esc;\n" +
				"public class MCIS2 {\n" + 
				"   //@ requires i > 0;\n" +
				"   //@ ensures \\result == i * i;\n" +
				"   public static int sq(int i) {\n" +
				"	   return i*i;\n" +
				"	}\n" +
				"   //@ requires i > 0;\n" +
				"   //@ ensures \\result == i * sq(i);\n" +
				"   public static int cube(int i) {\n" +
				"	   return i*i*i;\n" +
				"	}\n" +
				"   //@ requires i > 0;\n" +
				"   //@ requires j > 0;\n" +
				"   //@ ensures \\result == sq(i) * sq(j);\n" +
				"   public static int sq_sq(int i, int j) {\n" +
				"	   return i*i*j*j;\n" +
				"	}\n" +
				"   public static void m1() {\n" +
				"	   //@ assert (\\forall int i, j; i > 0 && i==j; sq_sq(i, j) == i * cube(j));\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}

	public void test_9000_passify_conditional() {
		this.runNegativeTest(new String[] {
				testsPath + "AE.java",
				"package tests.esc;\n" +
				"public class AE {\n" + 
				"   public static void m1(int i) {\n" +
				"	   int b = (++i < 0 ? -1 : (i*=2));\n" +
				"	   //@ assert (b == -1) ==> (i < 0);\n" +
				"	   //@ assert (b > 0) ==> (i >  0);\n" +
				"	}\n" +
				"   public static void m2(int i) {\n" +
				"	   int b = (++i - (i > 0 ? i+1 : i--) < 0 ? -1 : (i*=2));\n" +
				"	}\n" +
				"   public static void m3(int i) {\n" +
				"	   int b = (++i < 0 ? -1 - (i > 0 ? i+1 : i--) : (i*=2));\n" +
				"	}\n" +
				"   public static void m4(int i) {\n" +
				"	   int b = (++i < 0 ? -1 : (i*=2) - (i > 0 ? i+1 : i--));\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}

	public void test_9001() {
		this.runNegativeTest(new String[] {
				testsPath + "ProvablyFalse.java",
				"package tests.esc;\n" +
				"public class ProvablyFalse {\n" +
				"	//@ ensures \\result > 0 && \\result % 2 == 1;\n" +
				"	public int m() {\n" +
				"		return 42;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in " + testsPath + "ProvablyFalse.java (at line 3)\n" +
				"	//@ ensures \\result > 0 && \\result % 2 == 1;\n" +
				"	                           ^^^^^^^^^^^^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n");
	}
}