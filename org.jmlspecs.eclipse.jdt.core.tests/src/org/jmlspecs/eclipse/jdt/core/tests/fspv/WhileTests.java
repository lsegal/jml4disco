package org.jmlspecs.eclipse.jdt.core.tests.fspv;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.core.tests.util.Util;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class WhileTests extends AbstractRegressionTest {

	public WhileTests(String name) {
		super(name);
	}

	// Augment problem detection settings
	@Override
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
		Map<String, String> options = super.getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
		options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
		options.put(JmlCompilerOptions.OPTION_EnableJmlFspv, CompilerOptions.ENABLED);
		// options.put(JmlCompilerOptions.OPTION_SpecPath,
		// NullTypeSystemTestCompiler.getSpecPath());
		options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_Source, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_TargetPlatform, CompilerOptions.VERSION_1_5);
		return options;
	}

	//private final String testsPath = "tests" + File.separatorChar + "esc" + File.separatorChar;
	// the line above fails under linux.  the following works under both linux & cygwin.
	private final String testsPath = "tests" + '\\' + "fspv" + '\\';

	public void test_001_cube() {
		PrintStream stdout = System.out;
		ByteArrayOutputStream strOut=new ByteArrayOutputStream();
		System.setOut(new PrintStream(strOut));
		this.runNegativeTest(new String[] {
				testsPath + "WhileTestsCube.java",
				"package tests.fspv;\n" +
				"public class WhileTestsCube {\n" +
				"	//@ requires x > 0;\n" +
				"	//@ ensures  \\result == x * x * x;\n" +
				"	public int cube(int x) {\n" +
				"		int a = 1;\n" +
				"		int b = 0;\n" +
				"		int c = x;\n" +
				"		int z = 0;\n" +
				"		//@ maintaining a == 3*(x-c) + 1;\n" +
				"		//@ maintaining b == 3*(x-c)*(x-c);\n" +
				"		//@ maintaining z == (x-c)*(x-c)*(x-c);\n" +
				"		//@ decreasing c;\n" +
				"		while (c > 0) {\n" +
				"			z += a + b;\n" +
				"			b += 2*a + 1;\n" +
				"			a += 3;\n" +
				"			c -= 1;\n" +
				"		}\n" +
				"		//@ assert z == x * x * x;\n" +
				"		return z;\n" +
				"	}\n" +
				"}\n"
		},
		"",null, true);
		System.setOut(stdout);
		String actual =  Util.convertToIndependantLineDelimiter(strOut.toString());
		String expected = 
			"theory WhileTestsCube imports Vcg \n" +
			"begin\n" +
			"  hoarestate WhileTestsCube_cube_int_vars =\n" +
			"    result' :: int\n" +
			"    x :: int\n" +
			"    x_old :: int\n" +
			"    a :: int\n" +
			"    b :: int\n" +
			"    c :: int\n" +
			"    z :: int\n" +
			"  lemma (in WhileTestsCube_cube_int_vars) WhileTestsCube_cube_int: \"\n" +
			"  \\<Gamma> \\<turnstile>\n" +
			"    \\<lbrace> (\\<acute>x > 0) \\<rbrace>\n" +
			"    \\<acute>x_old :== \\<acute>x;;\n" +
			"    \\<acute>a :== 1;;\n" +
			"    \\<acute>b :== 0;;\n" +
			"    \\<acute>c :== \\<acute>x;;\n" +
			"    \\<acute>z :== 0;;\n" +
			"    WHILE (\\<acute>c > 0)\n" +
			"    INV \\<lbrace> (\\<acute>a = ((3 * (\\<acute>x - \\<acute>c)) + 1)) \\<and> (\\<acute>b = ((3 * (\\<acute>x - \\<acute>c)) * (\\<acute>x - \\<acute>c))) \\<and> (\\<acute>z = (((\\<acute>x - \\<acute>c) * (\\<acute>x - \\<acute>c)) * (\\<acute>x - \\<acute>c))) \\<and> (\\<acute>c \\<ge> 0) \\<and> (\\<acute>x = \\<acute>x_old) \\<rbrace>\n" +
			"    VAR MEASURE nat \\<acute>c\n" +
			"    DO\n" +
			"      \\<acute>z :== (\\<acute>z + (\\<acute>a + \\<acute>b));;\n" +
			"      \\<acute>b :== (\\<acute>b + ((2 * \\<acute>a) + 1));;\n" +
			"      \\<acute>a :== (\\<acute>a + 3);;\n" +
			"      \\<acute>c :== (\\<acute>c - 1)\n" +
			"    OD;;\n" +
			"    \\<acute>result' :== \\<acute>z\n" +
			"    \\<lbrace> (\\<acute>result' = ((\\<acute>x_old * \\<acute>x_old) * \\<acute>x_old)) \\<rbrace>\n" +
			"    \"\n" +
			"    apply(vcg)\n" +
			"    apply(auto)\n" +
			"    apply(algebra)+\n" +
			"  done\n" +
			"\n" +
			"end\n";
		assertEquals("", expected, actual);
	}

	public void test_002_sum() {
		PrintStream stdout = System.out;
		ByteArrayOutputStream strOut=new ByteArrayOutputStream();
		System.setOut(new PrintStream(strOut));
		this.runNegativeTest(new String[] {
				testsPath + "WhileTestsSum.java",
				"package tests.fspv;\n" +
				"public class WhileTestsSum {\n" +
				"	//@ requires b >= 0;\n" +
				"	//@ ensures \\result == a + b;\n" +
				"	public int sum(final int a, final int b) {\n" +
				"		int sum = a;\n" +
				"		int i = b;\n" +
				"		//@ maintaining sum == a + b - i;\n" +
				"		//@ maintaining i >= 0;\n" +
				"		//@ decreasing i;\n" +
				"		while (i != 0) {\n" +
				"			sum = sum + 1;\n" +
				"			i -= 1;\n" +
				"		}\n" +
				"		//x@ assert i == 0;\n" +
				"		return sum;\n" +
				"	}\n" +
				"}\n"
		},
		"", null, true);
		System.setOut(stdout);
		String actual =  Util.convertToIndependantLineDelimiter(strOut.toString());
		String expected = 
			"theory WhileTestsSum imports Vcg \n" +
			"begin\n" +
			"  hoarestate WhileTestsSum_sum_int_int_vars =\n" +
			"    result' :: int\n" +
			"    a :: int\n" +
			"    a_old :: int\n" +
			"    b :: int\n" +
			"    b_old :: int\n" +
			"    sum :: int\n" +
			"    i :: int\n" +
			"  lemma (in WhileTestsSum_sum_int_int_vars) WhileTestsSum_sum_int_int: \"\n" +
			"  \\<Gamma> \\<turnstile>\n" +
			"    \\<lbrace> (\\<acute>b \\<ge> 0) \\<rbrace>\n" +
			"    \\<acute>a_old :== \\<acute>a;;\n" +
			"    \\<acute>b_old :== \\<acute>b;;\n" +
			"    \\<acute>sum :== \\<acute>a;;\n" +
			"    \\<acute>i :== \\<acute>b;;\n" +
			"    WHILE (\\<acute>i \\<noteq> 0)\n" +
			"    INV \\<lbrace> (\\<acute>sum = ((\\<acute>a + \\<acute>b) - \\<acute>i)) \\<and> (\\<acute>i \\<ge> 0) \\<and> (\\<acute>i \\<ge> 0) \\<and> (\\<acute>a = \\<acute>a_old) \\<and> (\\<acute>b = \\<acute>b_old) \\<rbrace>\n" +
			"    VAR MEASURE nat \\<acute>i\n" +
			"    DO\n" +
			"      \\<acute>sum :== (\\<acute>sum + 1);;\n" +
			"      \\<acute>i :== (\\<acute>i - 1)\n" +
			"    OD;;\n" +
			"    \\<acute>result' :== \\<acute>sum\n" +
			"    \\<lbrace> (\\<acute>result' = (\\<acute>a_old + \\<acute>b_old)) \\<rbrace>\n" +
			"    \"\n" +
			"    apply(vcg)\n" +
			"    apply(auto)\n" +
			"    apply(algebra)+\n" +
			"  done\n" +
			"\n" +
			"end\n";
		assertEquals("", expected, actual);
	}

	public void test_003_comp() {
		PrintStream stdout = System.out;
		ByteArrayOutputStream strOut=new ByteArrayOutputStream();
		System.setOut(new PrintStream(strOut));
		this.runNegativeTest(new String[] {
				testsPath + "WhileTestsComp.java",
				"package tests.fspv;\n" +
				"public class WhileTestsComp {\n" +
				"	//@ requires y >= 0 && x >= 0;\n" +
				"	//@ ensures  \\result == x + y * y;\n" +
				"	public int m_22_comp(int x, int y) {\n" +
				"		int z = x;\n" +
				"		int w = y;\n" +
				"		//@ assert (y*w) + z == x + y * y;\n" +
				"		//@ maintaining z == x + y * y - w*y;\n" +
				"		//@ maintaining w >= 0;\n" +
				"		//@ decreasing w;\n" +
				"		while (w > 0) {\n" +
				"			z += y;\n" +
				"			w -= 1;\n" +
				"			//@ assert (y*w) + z == x + y * y;\n" +
				"		}\n" +
				"		return z;\n" +
				"	}\n" +
				"}\n"
		},
		"", null, true);
		System.setOut(stdout);
		String actual =  Util.convertToIndependantLineDelimiter(strOut.toString());
		String expected =
			"theory WhileTestsComp imports Vcg \n" +
			"begin\n" +
			"  hoarestate WhileTestsComp_m_22_comp_int_int_vars =\n" +
			"    result' :: int\n" +
			"    x :: int\n" +
			"    x_old :: int\n" +
			"    y :: int\n" +
			"    y_old :: int\n" +
			"    z :: int\n" +
			"    w :: int\n" +
			"  lemma (in WhileTestsComp_m_22_comp_int_int_vars) WhileTestsComp_m_22_comp_int_int: \"\n" +
			"  \\<Gamma> \\<turnstile>\n" +
			"    \\<lbrace> ((\\<acute>y \\<ge> 0) \\<and> (\\<acute>x \\<ge> 0)) \\<rbrace>\n" +
			"    \\<acute>x_old :== \\<acute>x;;\n" +
			"    \\<acute>y_old :== \\<acute>y;;\n" +
			"    \\<acute>z :== \\<acute>x;;\n" +
			"    \\<acute>w :== \\<acute>y;;\n" +
			"    WHILE (\\<acute>w > 0)\n" +
			"    INV \\<lbrace> (\\<acute>z = ((\\<acute>x + (\\<acute>y * \\<acute>y)) - (\\<acute>w * \\<acute>y))) \\<and> (\\<acute>w \\<ge> 0) \\<and> (\\<acute>w \\<ge> 0) \\<and> (\\<acute>x = \\<acute>x_old) \\<and> (\\<acute>y = \\<acute>y_old) \\<rbrace>\n" +
			"    VAR MEASURE nat \\<acute>w\n" +
			"    DO\n" +
			"      \\<acute>z :== (\\<acute>z + \\<acute>y);;\n" +
			"      \\<acute>w :== (\\<acute>w - 1)\n" +
			"    OD;;\n" +
			"    \\<acute>result' :== \\<acute>z\n" +
			"    \\<lbrace> (\\<acute>result' = (\\<acute>x_old + (\\<acute>y_old * \\<acute>y_old))) \\<rbrace>\n" +
			"    \"\n" +
			"    apply(vcg)\n" +
			"    apply(auto)\n" +
			"    apply(algebra)+\n" +
			"  done\n" +
			"\n" +
			"end\n";		
		assertEquals("", expected, actual);
	}

	public void test_004_WhileTests() {
		PrintStream stdout = System.out;
		ByteArrayOutputStream strOut=new ByteArrayOutputStream();
		System.setOut(new PrintStream(strOut));
		this.runNegativeTest(new String[] {
				testsPath + "WhileTests.java",
				"package tests.fspv;\n" +
				"public class WhileTests {\n" +
				"	//@ requires x > 0;\n" +
				"	//@ ensures  \\result == x * x * x;\n" +
				"	public int cube(int x) {\n" +
				"		int a = 1;\n" +
				"		int b = 0;\n" +
				"		int c = x;\n" +
				"		int z = 0;\n" +
				"		//@ maintaining a == 3*(x-c) + 1;\n" +
				"		//@ maintaining b == 3*(x-c)*(x-c);\n" +
				"		//@ maintaining z == (x-c)*(x-c)*(x-c);\n" +
				"		//@ decreasing c;\n" +
				"		while (c > 0) {\n" +
				"			z += a + b;\n" +
				"			b += 2*a + 1;\n" +
				"			a += 3;\n" +
				"			c -= 1;\n" +
				"		}\n" +
				"		//@ assert z == x * x * x;\n" +
				"		return z;\n" +
				"	}\n" +
				"\n" +
				"	//@ requires b >= 0;\n" +
				"	//@ ensures \\result == a + b;\n" +
				"	public int sum(final int a, final int b) {\n" +
				"		int sum = a;\n" +
				"		int i = b;\n" +
				"		//@ maintaining sum == a + b - i;\n" +
				"		//@ maintaining i >= 0;\n" +
				"		//@ decreasing i;\n" +
				"		while (i != 0) {\n" +
				"			sum = sum + 1;\n" +
				"			i -= 1;\n" +
				"		}\n" +
				"		//x@ assert i == 0;\n" +
				"		return sum;\n" +
				"	}\n" +
				"\n" +
				"	\n" +
				"	//@ requires y >= 0 && x >= 0;\n" +
				"	//@ ensures  \\result == x + y * y;\n" +
				"	public int m_22_comp(int x, int y) {\n" +
				"		int z = x;\n" +
				"		int w = y;\n" +
				"		//@ assert (y*w) + z == x + y * y;\n" +
				"		//@ maintaining z == x + y * y - w*y;\n" +
				"		//@ maintaining w >= 0;\n" +
				"		//@ decreasing w;\n" +
				"		while (w > 0) {\n" +
				"			z += y;\n" +
				"			w -= 1;\n" +
				"			//@ assert (y*w) + z == x + y * y;\n" +
				"		}\n" +
				"		return z;\n" +
				"	}\n" +
				"}\n"
		},
		"", null, true);
		System.setOut(stdout);
		String actual =  Util.convertToIndependantLineDelimiter(strOut.toString());
		String expected = 
			"theory WhileTests imports Vcg \n" +
			"begin\n" +
			"  hoarestate WhileTests_cube_int_vars =\n" +
			"    result' :: int\n" +
			"    x :: int\n" +
			"    x_old :: int\n" +
			"    a :: int\n" +
			"    b :: int\n" +
			"    c :: int\n" +
			"    z :: int\n" +
			"  lemma (in WhileTests_cube_int_vars) WhileTests_cube_int: \"\n" +
			"  \\<Gamma> \\<turnstile>\n" +
			"    \\<lbrace> (\\<acute>x > 0) \\<rbrace>\n" +
			"    \\<acute>x_old :== \\<acute>x;;\n" +
			"    \\<acute>a :== 1;;\n" +
			"    \\<acute>b :== 0;;\n" +
			"    \\<acute>c :== \\<acute>x;;\n" +
			"    \\<acute>z :== 0;;\n" +
			"    WHILE (\\<acute>c > 0)\n" +
			"    INV \\<lbrace> (\\<acute>a = ((3 * (\\<acute>x - \\<acute>c)) + 1)) \\<and> (\\<acute>b = ((3 * (\\<acute>x - \\<acute>c)) * (\\<acute>x - \\<acute>c))) \\<and> (\\<acute>z = (((\\<acute>x - \\<acute>c) * (\\<acute>x - \\<acute>c)) * (\\<acute>x - \\<acute>c))) \\<and> (\\<acute>c \\<ge> 0) \\<and> (\\<acute>x = \\<acute>x_old) \\<rbrace>\n" +
			"    VAR MEASURE nat \\<acute>c\n" +
			"    DO\n" +
			"      \\<acute>z :== (\\<acute>z + (\\<acute>a + \\<acute>b));;\n" +
			"      \\<acute>b :== (\\<acute>b + ((2 * \\<acute>a) + 1));;\n" +
			"      \\<acute>a :== (\\<acute>a + 3);;\n" +
			"      \\<acute>c :== (\\<acute>c - 1)\n" +
			"    OD;;\n" +
			"    \\<acute>result' :== \\<acute>z\n" +
			"    \\<lbrace> (\\<acute>result' = ((\\<acute>x_old * \\<acute>x_old) * \\<acute>x_old)) \\<rbrace>\n" +
			"    \"\n" +
			"    apply(vcg)\n" +
			"    apply(auto)\n" +
			"    apply(algebra)+\n" +
			"  done\n" +
			"\n" +
			"  hoarestate WhileTests_sum_int_int_vars =\n" +
			"    result' :: int\n" +
			"    a :: int\n" +
			"    a_old :: int\n" +
			"    b :: int\n" +
			"    b_old :: int\n" +
			"    sum :: int\n" +
			"    i :: int\n" +
			"  lemma (in WhileTests_sum_int_int_vars) WhileTests_sum_int_int: \"\n" +
			"  \\<Gamma> \\<turnstile>\n" +
			"    \\<lbrace> (\\<acute>b \\<ge> 0) \\<rbrace>\n" +
			"    \\<acute>a_old :== \\<acute>a;;\n" +
			"    \\<acute>b_old :== \\<acute>b;;\n" +
			"    \\<acute>sum :== \\<acute>a;;\n" +
			"    \\<acute>i :== \\<acute>b;;\n" +
			"    WHILE (\\<acute>i \\<noteq> 0)\n" +
			"    INV \\<lbrace> (\\<acute>sum = ((\\<acute>a + \\<acute>b) - \\<acute>i)) \\<and> (\\<acute>i \\<ge> 0) \\<and> (\\<acute>i \\<ge> 0) \\<and> (\\<acute>a = \\<acute>a_old) \\<and> (\\<acute>b = \\<acute>b_old) \\<rbrace>\n" +
			"    VAR MEASURE nat \\<acute>i\n" +
			"    DO\n" +
			"      \\<acute>sum :== (\\<acute>sum + 1);;\n" +
			"      \\<acute>i :== (\\<acute>i - 1)\n" +
			"    OD;;\n" +
			"    \\<acute>result' :== \\<acute>sum\n" +
			"    \\<lbrace> (\\<acute>result' = (\\<acute>a_old + \\<acute>b_old)) \\<rbrace>\n" +
			"    \"\n" +
			"    apply(vcg)\n" +
			"    apply(auto)\n" +
			"    apply(algebra)+\n" +
			"  done\n" +
			"\n" +
			"  hoarestate WhileTests_m_22_comp_int_int_vars =\n" +
			"    result' :: int\n" +
			"    x :: int\n" +
			"    x_old :: int\n" +
			"    y :: int\n" +
			"    y_old :: int\n" +
			"    z :: int\n" +
			"    w :: int\n" +
			"  lemma (in WhileTests_m_22_comp_int_int_vars) WhileTests_m_22_comp_int_int: \"\n" +
			"  \\<Gamma> \\<turnstile>\n" +
			"    \\<lbrace> ((\\<acute>y \\<ge> 0) \\<and> (\\<acute>x \\<ge> 0)) \\<rbrace>\n" +
			"    \\<acute>x_old :== \\<acute>x;;\n" +
			"    \\<acute>y_old :== \\<acute>y;;\n" +
			"    \\<acute>z :== \\<acute>x;;\n" +
			"    \\<acute>w :== \\<acute>y;;\n" +
			"    WHILE (\\<acute>w > 0)\n" +
			"    INV \\<lbrace> (\\<acute>z = ((\\<acute>x + (\\<acute>y * \\<acute>y)) - (\\<acute>w * \\<acute>y))) \\<and> (\\<acute>w \\<ge> 0) \\<and> (\\<acute>w \\<ge> 0) \\<and> (\\<acute>x = \\<acute>x_old) \\<and> (\\<acute>y = \\<acute>y_old) \\<rbrace>\n" +
			"    VAR MEASURE nat \\<acute>w\n" +
			"    DO\n" +
			"      \\<acute>z :== (\\<acute>z + \\<acute>y);;\n" +
			"      \\<acute>w :== (\\<acute>w - 1)\n" +
			"    OD;;\n" +
			"    \\<acute>result' :== \\<acute>z\n" +
			"    \\<lbrace> (\\<acute>result' = (\\<acute>x_old + (\\<acute>y_old * \\<acute>y_old))) \\<rbrace>\n" +
			"    \"\n" +
			"    apply(vcg)\n" +
			"    apply(auto)\n" +
			"    apply(algebra)+\n" +
			"  done\n" +
			"\n" +
			"end\n";		
		assertEquals("", expected, actual);
	}

	public void test_005_simple() {
		PrintStream stdout = System.out;
		ByteArrayOutputStream strOut=new ByteArrayOutputStream();
		System.setOut(new PrintStream(strOut));
		String programFile = 
			"package tests.fspv;\n" +
			"public class SimpleWhile {\n"+
			"  public void m_001(int x) {\n"+
			"    int i=0;\n"+
			"    while(i<x) \n"+
			"      x*=x;\n"+
			"  }\n"+
			"}\n";
		this.runNegativeTest(new String[] { testsPath + "SimpleWhile.java", programFile	}, "", null, true);
		System.setOut(stdout);
		String actual =  Util.convertToIndependantLineDelimiter(strOut.toString());
		String expected = 
			"theory SimpleWhile imports Vcg \n" +
			"begin\n" +
			"  hoarestate SimpleWhile_m_001_int_vars =\n" +
			"    x :: int\n" +
			"    x_old :: int\n" +
			"    i :: int\n" +
			"  lemma (in SimpleWhile_m_001_int_vars) SimpleWhile_m_001_int: \"\n" +
			"  \\<Gamma> \\<turnstile>\n" +
			"    \\<lbrace> True \\<rbrace>\n" +
			"    \\<acute>x_old :== \\<acute>x;;\n" +
			"    \\<acute>i :== 0;;\n" +
			"    WHILE (\\<acute>i < \\<acute>x)\n" +
			"    DO\n" +
			"      \\<acute>x :== (\\<acute>x * \\<acute>x)\n" +
			"    OD\n" +
			"    \\<lbrace> True \\<rbrace>\n" +
			"    \"\n" +
			"    apply(vcg)\n" +
			"    apply(auto)\n" +
			"    apply(algebra)+\n" +
			"  done\n" +
			"\n" +
			"end\n";
		assertEquals("", expected, actual);
	}

}
