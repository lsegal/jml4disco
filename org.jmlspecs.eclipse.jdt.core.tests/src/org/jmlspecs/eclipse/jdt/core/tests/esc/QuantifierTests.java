package org.jmlspecs.eclipse.jdt.core.tests.esc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.PostProcessor;

public class QuantifierTests extends AbstractRegressionTest {
	public QuantifierTests(String name) {
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

	public void test_0001_simple() {
		this.runNegativeTest(new String[] {
				testsPath + "Quant1.java",
				"package tests.esc;\n" +
				"public class Quant1 {\n" +
				"   public void m1() {\n" + 
				"      //@ assert (\\exists int i,j; 0 <= i & j < 10; i < j);\n" + 
				"      //@ assert (\\exists int i,j; j <= 5 & i > 10; i < j);\n" + 
				"      //@ assert (\\forall int i; 0 < i ; 0 <= i);\n" + 
				"      //@ assert (\\forall int i; 0 < i ; i <= 0);\n" + 
				"   }\n" + "}\n" 
				},
				"----------\n" + 
				"1. ERROR in "+testsPath+"Quant1.java (at line 5)\n" + 
				"	//@ assert (\\exists int i,j; j <= 5 & i > 10; i < j);\n" +
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in "+testsPath+"Quant1.java (at line 7)\n" + 
				"	//@ assert (\\forall int i; 0 < i ; i <= 0);\n" +
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}
	
	public void test_0002_and_and() {
		this.runNegativeTest(new String[] {
				testsPath + "Quant2.java",
				"package tests.esc;\n" +
				"public class Quant2 {\n" +
				"   public void m2() {\n" + 
				"      //@ assert (\\exists int i,j; 0 <= i && j < 10; i < j);\n" + 
				"      //@ assert (\\exists int i,j; j <= 5 && i > 10; i < j);\n" + 
				"   }\n" + "}\n" 
				},
				"----------\n" + 
				"1. ERROR in "+testsPath+"Quant2.java (at line 5)\n" + 
				"	//@ assert (\\exists int i,j; j <= 5 && i > 10; i < j);\n" +
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}

	public void test_0003_inConditional() {
		this.runNegativeTest(new String[] {
				testsPath + "Quant3.java",
				"package tests.esc;\n" +
				"public class Quant3 {\n" +
				"   public void m3(int i, int j) {\n" +
				"		/*@ assert ( i > j\n" +
				"		  @      ?  (\\forall int k ; i + k >  j + k )\n" +
				"		  @      :  (\\forall int k ; i + k <= j + k ));\n" +
				"		  @*/\n" +
				"	}\n" +
				"   public void m4 (int i, int j) {\n" +
				"		/*@ assert ( i > j\n" +
				"		  @      ?  (\\forall int k ; i + k > j + k )\n" +
				"		  @      :  (\\forall int k ; i + k > j + k ));\n" +
				"		  @*/\n" +
				"	}\n" +
				"}\n" 
				},
				"----------\n" + 
				"1. ERROR in tests\\esc\\Quant3.java (at line 10)\n" + 
				"	/*@ assert ( i > j\n" + 
				"		  @      ?  (\\forall int k ; i + k > j + k )\n" + 
				"		  @      :  (\\forall int k ; i + k > j + k ));\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}

	public void test_0100_sum() {
		this.runNegativeTest(new String[] {
				testsPath + "Quant100.java",
				"package tests.esc;\n" +
				"public class Quant100 {\n" +
				"   public void m1() {\n" +
				"		//@ assert 5 == (\\sum int i ; 2 <= i && i <= 3; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 2 <= i && i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <  i && i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 2 <= i &  i <= 3; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 2 <= i &  i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <  i &  i <  4; i);\n" +
				"	}\n" +
				"   public void m2() {\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <= i && i <= 3; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <= i && i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 0 <  i && i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <= i &  i <= 3; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <= i &  i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 0 <  i &  i <  4; i);\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" + 
				"1. ERROR in tests\\esc\\Quant100.java (at line 12)\n" + 
				"	//@ assert 5 == (\\sum int i ; 1 <= i && i <= 3; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in tests\\esc\\Quant100.java (at line 13)\n" + 
				"	//@ assert 5 == (\\sum int i ; 1 <= i && i <  4; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in tests\\esc\\Quant100.java (at line 14)\n" + 
				"	//@ assert 5 == (\\sum int i ; 0 <  i && i <  4; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"4. ERROR in tests\\esc\\Quant100.java (at line 15)\n" + 
				"	//@ assert 5 == (\\sum int i ; 1 <= i &  i <= 3; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"5. ERROR in tests\\esc\\Quant100.java (at line 16)\n" + 
				"	//@ assert 5 == (\\sum int i ; 1 <= i &  i <  4; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"6. ERROR in tests\\esc\\Quant100.java (at line 17)\n" + 
				"	//@ assert 5 == (\\sum int i ; 0 <  i &  i <  4; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}

	public void test_0110_product() {
		this.runNegativeTest(new String[] {
				testsPath + "Quant110.java",
				"package tests.esc;\n" +
				"public class Quant110 {\n" +
				"   public void m1() {\n" +
				"		//@ assert 6 == (\\product int i ; 2 <= i && i <= 3; i);\n" +
				"		//@ assert 6 == (\\product int i ; 2 <= i && i <  4; i);\n" +
				"		//@ assert 6 == (\\product int i ; 1 <  i && i <  4; i);\n" +
				"		//@ assert 6 == (\\product int i ; 2 <= i &  i <= 3; i);\n" +
				"		//@ assert 6 == (\\product int i ; 2 <= i &  i <  4; i);\n" +
				"		//@ assert 6 == (\\product int i ; 1 <  i &  i <  4; i);\n" +
				"	}\n" +
				"   public void m2() {\n" +
				"		//@ assert 5 == (\\product int i ; 1 <= i && i <= 3; i);\n" +
				"		//@ assert 5 == (\\product int i ; 1 <= i && i <  4; i);\n" +
				"		//@ assert 5 == (\\product int i ; 0 <  i && i <  4; i);\n" +
				"		//@ assert 5 == (\\product int i ; 1 <= i &  i <= 3; i);\n" +
				"		//@ assert 5 == (\\product int i ; 1 <= i &  i <  4; i);\n" +
				"		//@ assert 5 == (\\product int i ; 0 <  i &  i <  4; i);\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" + 
				"1. ERROR in tests\\esc\\Quant110.java (at line 12)\n" + 
				"	//@ assert 5 == (\\product int i ; 1 <= i && i <= 3; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in tests\\esc\\Quant110.java (at line 13)\n" + 
				"	//@ assert 5 == (\\product int i ; 1 <= i && i <  4; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in tests\\esc\\Quant110.java (at line 14)\n" + 
				"	//@ assert 5 == (\\product int i ; 0 <  i && i <  4; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"4. ERROR in tests\\esc\\Quant110.java (at line 15)\n" + 
				"	//@ assert 5 == (\\product int i ; 1 <= i &  i <= 3; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"5. ERROR in tests\\esc\\Quant110.java (at line 16)\n" + 
				"	//@ assert 5 == (\\product int i ; 1 <= i &  i <  4; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"6. ERROR in tests\\esc\\Quant110.java (at line 17)\n" + 
				"	//@ assert 5 == (\\product int i ; 0 <  i &  i <  4; i);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}

	public void test_0140_num_of() {
		this.runNegativeTest(new String[] {
				testsPath + "Quant140.java",
				"package tests.esc;\n" +
				"public class Quant140 {\n" +
				"   public void m1() {\n" +
				"		//@ assert 1 == (\\num_of int i ; 2 <= i && i <= 3; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 2 <= i && i <  4; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 1 <  i && i <  4; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 2 <= i &  i <= 3; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 2 <= i &  i <  4; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 1 <  i &  i <  4; i % 2 == 0);\n" +
				"	}\n" +
				"   public void m2() {\n" +
				"		//@ assert 2 == (\\num_of int i ; 2 <= i && i <= 3; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 2 <= i && i <  4; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 1 <  i && i <  4; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 2 <= i &  i <= 3; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 2 <= i &  i <  4; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 1 <  i &  i <  4; i % 2 == 0);\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" + 
				"1. ERROR in tests\\esc\\Quant140.java (at line 12)\n" + 
				"	//@ assert 2 == (\\num_of int i ; 2 <= i && i <= 3; i % 2 == 0);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"2. ERROR in tests\\esc\\Quant140.java (at line 13)\n" + 
				"	//@ assert 2 == (\\num_of int i ; 2 <= i && i <  4; i % 2 == 0);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in tests\\esc\\Quant140.java (at line 14)\n" + 
				"	//@ assert 2 == (\\num_of int i ; 1 <  i && i <  4; i % 2 == 0);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"4. ERROR in tests\\esc\\Quant140.java (at line 15)\n" + 
				"	//@ assert 2 == (\\num_of int i ; 2 <= i &  i <= 3; i % 2 == 0);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"5. ERROR in tests\\esc\\Quant140.java (at line 16)\n" + 
				"	//@ assert 2 == (\\num_of int i ; 2 <= i &  i <  4; i % 2 == 0);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"6. ERROR in tests\\esc\\Quant140.java (at line 17)\n" + 
				"	//@ assert 2 == (\\num_of int i ; 1 <  i &  i <  4; i % 2 == 0);\n" + 
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}

	public void test_0150_fromRefMan() {
		this.runNegativeTest(new String[] {
				testsPath + "Quant150.java",
				"package tests.esc;\n" +
				"public class Quant150 {\n" +
				"   public void m1() {\n" + 
				"		//@ assert (\\sum int i; 0 <= i && i < 5; i) == 0 + 1 + 2 + 3 + 4;\n" +
				"		//@ assert (\\product int i; 0 < i && i < 5; i) == 1 * 2 * 3 * 4;\n" +
				"		//@ assert (\\max int i; 0 <= i && i < 5; i) == 4;\n" +
				"		//@ assert (\\min int i; 0 <= i && i < 5; i-1) == -1;\n" +
				"\n" +
				"		//@ assert (\\sum int i; i == 0x7fffffff || i == 1; i) == 0x7fffffff + 1;\n" +
				"//		//@ assert (\\sum int i; i == 0x7fffffff || i == 1; i) == 0x80000000;\n" +
				"\n" +
				"		//@ assert (\\sum int i; false; i) == 0;\n" +
				"\n" +
				"		//@ assert (\\num_of int i; 0 <= i & i <= 10; i * i == 9) == 1;\n" +
				"		//@ assert 2 == (\\num_of int i; 0 <= i & i <= 10; i * i == i + i);\n" +
				"   }\n" +
				"}\n" 
				},
				"");
	}
	public void test_1000_methodCall() {
		this.runNegativeTest(new String[] {
			testsPath + "Quant_MC.java",
			"package tests.esc;\n" +
			"public class Quant_MC{\n" +
			"   //@ requires b >= 0;\n" +
			"   //@ requires a > 0;\n" +
			"   //@ ensures  \\result == (b % a == 0);\n" +
			"   public static boolean divides(int a, int b) {\n" +
			"      return (b - (b/a)*a) == 0;\n" +
			"   }\n" +
			"\n" +
			"	//@ requires 0 < c;\n" +
			"   //@ requires 0 < a;\n" +
			"   //@ requires 0 < i;\n" +
			"   //@ requires c < a;\n" +
			"   //@ requires c <= a;\n" +
			"   //@ requires 0 <= a-i+1;\n" +
			"   public static void m(int c, int a, int i) {\n" +
			"      /*@ assume (\\forall int d;\n" +
			"        @                 (0 < d) & (d <= i);\n" +
			"        @                 divides(d, a)\n" +
			"        @                    ==> d <= c);\n" +
			"        @*/\n" +
			"      /*@ assert (\\forall int e;\n" +
			"        @                 (0 < e) & (e <= i);\n" +
			"        @                 divides(e, a)\n" +
			"        @                    ==> e <= c);\n" +
			"        @*/\n" +
			"   }\n" +
			"}\n"},
			"");
	}

	public void _test_1010_methodCall_sum() {
		this.runNegativeTest(new String[] {
				testsPath + "mcn.java",
				"package tests.esc;\n" +
				"public class mcn {\n" +
				"	//@ensures \\result == (3 * x);\n" +
				"	public int tripple(int x) {\n" +
				"		return x + x + x;\n" +
				"	}\n" +
				"	public void m() {\n" +
				"		//@ assert 2*3 + 3*3 == (\\sum int x; 1 < x & x < 4; tripple(x));\n" +
				"	}\n" +
				"}\n" 
				},
				"----------\n" + 
				"----------\n");
	}
 }
