package org.jmlspecs.eclipse.jdt.core.tests.esc.distributed;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.PostProcessor;
import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcDistributed;

public class BigWhileTests extends AbstractRegressionTest {
	public BigWhileTests(String name) {
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
		options.put(JmlCompilerOptions.OPTION_EscDistributedPropertiesFile, "proverCoordinatorUrls.properties");
		options.put(JmlCompilerOptions.OPTION_EscProverStrategy, ProveVcDistributed.getName());
		return options;
	}

//	private final String testsPath = "tests" + File.separatorChar + "esc" + File.separatorChar;
	// the line above fails under linux.  the following works under both linux & cygwin.
	private final String testsPath = "tests" + '\\' + "esc" + '\\';

	public void test_000_assertFalse() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assert false;\n" + 
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result == 0;\n" +
				"   public int m1(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result != 0;\n" +
				"   public int m2(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result != 0;\n" +
				"   public int m3(int x)\n" +
				"   {\n" +
				"      //@ assert false;\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-2;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result == 0;\n" +
				"   public int m1a(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result != 0;\n" +
				"   public int m2a(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result != 0;\n" +
				"   public int m3b(int x)\n" +
				"   {\n" +
				"      //@ assert false;\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-2;\n" +
				"      return x;\n" +
				"   }\n" +
				"   public void md(boolean b, boolean p) {\n" +
				"      while (b) {\n" +
				"            if (p) {\n" +
				"               break;\n" +
				"            }\n" +
				"      }\n" +
				"   }\n" +
				"  //@ requires i;" +
				"  public void m_break_2d(boolean b, boolean i) {\n" +
				"      if (b) {\n" +
				"          //@ loop_invariant i;\n" +
				"          while (b) {\n" +
				"              //@ assert b & i;\n" +
				"              break;\n" +
				"          }\n" +
				"      }\n" +
				"  }\n" +
				"  //@ requires i & j;" +
				"  //@ ensures  b & i & j;" +
				"  public void m_break_3d(boolean b, boolean i, boolean j) {\n" +
				"      if (b) {\n" +
				"          //@ loop_invariant i;\n" +
				"          while (b) {\n" +
				"              //@ assert b & i & j;\n" +
				"              break;\n" +
				"          }\n" +
				"          //@ assert b & i & j; // we know b\n" +
				"      }\n" +
				"      //@ assert b & i & j; // we don't know b\n" +
				"  }\n" +
				"  //@ requires i & j;" +
				"  public void m_break_4d(boolean b, boolean i, boolean j) {\n" +
				"      if (b) {\n" +
				"          //@ loop_invariant i;\n" +
				"          while (b) {\n" +
				"              //@ assert b & i & j;\n" +
				"              break;\n" +
				"          }\n" +
				"      }\n" +
				"  }\n" +
				"  //@ requires 100 <= y;\n" +
				"  public static int m4d(int y) {\n" +
				"    //@ loop_invariant 0 <= y;\n" +
				"    while (0 < y) {\n" +
				"          //@ assert true;\n" +
				"          if (y<0) {\n" +
				"             //@ assert true;\n" +
				"             break;\n" +
				"          }\n" +
				"          y = y - 1;\n" +
				"          //@ assert 0 <= y;\n" +
				"    }\n" +
				"    //@ assert false; // here\n" +
				"    return y;\n" +
				"  }\n" +
				"  //@ requires i & j;\n" +
				"  //@ ensures  i & j & b;\n" +
				"  public void m_break_1d(boolean b, boolean i, boolean j) {\n" +
				"      //@ loop_invariant i;\n" +
				"      while (b) {\n" +
				"          //@ assert b;\n" +
				"          //@ assert i;\n" +
				"          //@ assert j;\n" +
				"          break;\n" +
				"      }\n" +
				"  }\n" +
				"	//@ requires j;\n" +
				"   public static void m_while_1e(boolean b, boolean j) {\n" +
				"		if (b) {\n" +
				"			//@ assert b & j;\n" +
				"			while (true) {\n" +
				"				j = false;\n" +
				"				break;\n" +
				"			}\n" +
				"			//@ assert b & !j;\n" +
				"		} else {\n" +
				"			//@ assert !b & j;\n" +
				"		}\n" +
				"		//@ assert j;\n" +
				"	}\n" +
				"	//@ requires j;\n" +
				"   public static void m_while_2e(boolean b, boolean j) {\n" +
				"		if (b) {\n" +
				"			//@ assert b & j;\n" +
				"			while (true) {\n" +
				"				j = false;\n" +
				"				break;\n" +
				"			}\n" +
				"			//@ assert b & !j;\n" +
				"		} else {\n" +
				"			//@ assert !b & j;\n" +
				"		}\n" +
				"		//@ assert (b & !j) | (!b & j);\n" +
				"	}\n" +
				"   public static void m0f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 0;\n" +
				"		while (i > 0) {\n" +
				"             i--;\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"	}\n" +
				"   public static void m1f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i > 0;\n" +
				"		while (--i > 0) {\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"	}\n" +
				"   public static void m2f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 3;\n" +
				"		while (i-- > 3) {\n" +
				"		}\n" +
				"		//@ assert i == 2;\n" +
				"	}\n" +
				"   public static void m3f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 0;\n" +
				"		while (--i > 0) {\n" +
				"		}\n" +
				"		//@ assert i == 4;\n" +
				"	}\n" +
				"   public static void m4f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 0;\n" +
				"		while (i-- > 1) {\n" +
				"		}\n" +
				"		//@ assert i == 1;\n" +
				"	}\n" +
				"   public static void m1g() {\n" +
				"		int a = 10;\n" +
				"		//@ decreases a;\n" +
				"		while (a > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m2g() {\n" +
				"		int b = 10;\n" +
				"		//@ decreases b;\n" +
				"		while (b > 0) {\n" +
				"             b--;\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m3g() {\n" +
				"		int c = 10;\n" +
				"		//@ decreases c;\n" +
				"		while (c > 0) {\n" +
				"             c++;\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m4g() {\n" +
				"		int d = 10;\n" +
				"		//@ decreases d;\n" +
				"		while (--d > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m5g() {\n" +
				"		int e = 10;\n" +
				"		//@ decreases e;\n" +
				"		while (++e > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m6g() {\n" +
				"		int f = 10;\n" +
				"		//@ decreases f;\n" +
				"		while (f-- > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m7g() {\n" +
				"		int g = 10;\n" +
				"		//@ decreases g;\n" +
				"		while (g++ > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m8g(boolean b) {\n" +
				"		int h = 10;\n" +
				"		//@ decreases h;\n" +
				"		while (h > 0) {\n" +
				"             if (b) {\n" +
				"                h--;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m9g() {\n" +
				"		int i = 10;\n" +
				"		boolean b = true;\n" +
				"		//@ decreases i;\n" +
				"		while (i > 0) {\n" +
				"             if (b) {\n" +
				"                i--;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m1h(boolean b) {\n" +
				"		int i = 10;\n" +
				"		//@ decreases i;\n" +
				"		while (i > 0) {\n" +
				"             if (b) {\n" +
				"                i--;\n" +
				"                continue;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m2h() {\n" +
				"		int j = 10;\n" +
				"		boolean c = (j / 5 == 2);\n" +
				"		//@ decreases j;\n" +
				"		while (j > 0) {\n" +
				"             if (c) {\n" +
				"                j--;\n" +
				"                continue;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"	//@ requires b >= 0;\n" +
				"	//@ ensures \\result == a + b;\n" +
				"	public int sum1(final int a, final int b) {\n" +
				"		int sum = a;\n" +
				"		int i = b;\n" +
				"		//@ maintaining sum == a + b - i;\n" +
				"		//@ maintaining i >= 0;\n" +
				"		//@ decreasing i;\n" +
				"		while (i != 0) {\n" +
				"			sum++;\n" +
				"			i -= 1;\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"		return sum;\n" +
				"	}\n" + 
				"	//@ requires b >= 0;\n" +
				"	//@ ensures \\result == a + b;\n" +
				"	public int sum2(final int a, final int b) {\n" +
				"		int sum = a;\n" +
				"		int i = b;\n" +
				"		//@ maintaining sum == a + b - i;\n" +
				"		//@ decreasing i;\n" +
				"		while (i != 0) {\n" +
				"			sum++;\n" +
				"			i -= 1;\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"		return sum;\n" +
				"	}\n" + 
				"	//@ requires b >= 0;\n" +
				"	//@ ensures \\result == a + b + 1;\n" +
				"	public int sum1b(final int a, final int b) {\n" +
				"		int sum = a;\n" +
				"		int i = b;\n" +
				"		//@ maintaining sum == a + b - i;\n" +
				"		//@ maintaining i+1 >= 0;\n" +
				"		//@ decreasing i+1;\n" +
				"		while (i-- >= 0) {\n" +
				"			sum++;\n" +
				"		}\n" +
				"		//@ assert i == -2;\n" +
				"		return sum;\n" +
				"	}\n" + 
				"	//@ requires b >= 0;\n" +
				"	public void noSideEffects(int b) {\n" +
				"		int i = b;\n" +
				"		//@ maintaining i+1 >= 0;\n" +
				"		//@ decreasing i+1;\n" +
				"		while (i >= 0) {\n" +
				"		      i--;\n" +
				"		}\n" +
				"		//@ assert i == -1;\n" +
				"	}\n" + 
				"	//@ requires b >= 0;\n" +
				"	public void sum1c(final int b) {\n" +
				"		int i = b;\n" +
				"		//@ maintaining i+1 >= 0;\n" +
				"		//@ decreasing i+1;\n" +
				"		while (i-- >= 0) {\n" +
				"		}\n" +
				"		//@ assert i == -2;\n" +
				"	}\n" + 
				"	public int m1i() {\n" +
				"		int m=10;\n" +
				"		//@ maintaining m >= 0;\n" +
				"		while (m > 0) {\n" +
				"		      m = m - 1;\n" +
				"		}\n" +
				"		//@ assert m == 0;\n" +
				"		return m;\n" +
				"	}\n" +
				"	public int m2i() {\n" +
				"		int m=10;\n" +
				"		//@ maintaining m >= 0;\n" +
				"		while (m-- > 1) {\n" +
				"		}\n" +
				"		//@ assert m == 0;\n" +
				"		return m;\n" +
				"	}\n" +
				"	public int m3i() {\n" +
				"		int m=10;\n" +
				"		//@ maintaining m >= 0;\n" +
				"		while (m-- > 2) {\n" +
				"		}\n" +
				"		//@ assert m == 0;\n" +
				"		//@ assert false;\n" +
				"		return m;\n" +
				"	}\n" +
				"	//@ requires j;\n" +
				"   public static void m1j(boolean b, boolean j) {\n" +
				"      if (b) {\n" +
				"         //@ assert b & j;\n" +
				"         //@ loop_invariant b;\n" +
				"         while (true) {\n" +
				"            j = false;\n" +
				"         	break;\n" +
				"         }\n" +
				"         //@ assert !j;\n" +
				"         //@ assert  b;\n" +
				"      }\n" +
				"   }\n" +
				"	//@ requires j;\n" +
				"   public static void m1k(boolean b, boolean j) {\n" +
				"      if (b) {\n" +
				"         //@ assert b & j;\n" +
				"         //@ loop_invariant b;\n" +
				"         while (true) {\n" +
				"            j = false;\n" +
				"         	break;\n" +
				"         }\n" +
				"         //@ assert !j;\n" +
				"      }\n" +
				"      //@ assert b;\n" +
				"   }\n" +
				"   //@ requires j;\n" +
				"   public static void m2l(boolean b, boolean j) {\n" +
				"      if (b) {\n" +
				"         //@ assert b & j;\n" +
				"         if (true) {\n" +
				"            j = false;\n" +
				"         } else {\n" +
				"          b = true;\n" + // redundant info to change incarnation
				"         }\n" +
				"      //@ assert !j;\n" +
				"      //@ assert  b;\n" +
				"      }\n" +
				"      //@ assert b;\n" +
				"   }\n" +
				"	//@ requires y >= 0 && x >= 0;\n" +
				"	//@ ensures  \\result == x + y * y;\n" +
				"	public int m_22_comp(int x, int y) {\n" +
				"		int z = x;\n" +
				"		int w = y;\n" +
				"\n" +
				"		//@ assert (y*w) + z == x + y * y;\n" +
				"\n" +
				"		//@ maintaining z == x + y * y - w*y;\n" +
				"		//@ decreasing w;\n" +
				"		while (w > 0) {\n" +
				"			z += y;\n" +
				"			w--;\n" +
				"			//@ assert (y*w) + z == x + y * y;\n" +
				"		}\n" +
				"		return z;\n" +
				"	}\n" +
				"	//@ requires y > 0;\n" +
				"	//@ ensures  \\result == x - y;\n" +
				"	public int m_23_diff(int x, int y) {\n" +
				"		int z = x;\n" +
				"		int w = y;\n" +
				"		//@ maintaining x -y == z - w;\n" +
				"		//@ maintaining w >= 0;\n" +
				"		while (w > 0) {\n" +
				"			z--;\n" +
				"			w--;\n" +
				"		}\n" +
				"		return z;\n" +
				"	}\n" +
				"	//@ requires x >= 0 && y >= 0;\n" +
				"	//@ ensures  \\result == x * y;\n" +
				"	public int m_24_times(int x, int y) {\n" +
				"		int z = 0;\n" +
				"		int w = y;\n" +
				"		//@ assert w >= 0;\n" +
				"		//@ assert z == x*y - x*w;\n" +
				"\n" +
				"		//@ maintaining w >= 0;\n" +
				"		//@ maintaining z == x*y - x*w;\n" +
				"		while (w > 0) {\n" +
				"			z += x;\n" +
				"			w--;\n" +
				"		    //@ assert w >= 0;\n" +
				"		    //@ assert z == x*y - x*w;\n" +
				"		}\n" +
				"		//@ assert w >= 0;\n" +
				"		return z;\n" +
				"	}\n" +
				"	//@ requires x >= 0 && y > 0;\n" +
				"	//@ ensures  \\result == x * y * y;\n" +
				"	public int m_24_power(int x, int y) {\n" +
				"		int z = 0;\n" +
				"		int w = y;\n" +
				"		//@ assert z+(x*w) == x*y;\n" +
				"\n" +
				"		//@ maintaining w >= 0;\n" +
				"		//@ maintaining z+(x*w) == x*y;\n" +
				"		while (w > 0) {\n" +
				"			z += x;\n" +
				"			w--;\n" +
				"			//@ assert z+(x*w) == x*y;\n" +
				"		}\n" +
				"		w = y-1;\n" +
				"		int u = z;\n" +
				"\n" +
				"		//@ assert z+(x*y*w) == x*y*y;\n" +
				"\n" +
				"		//@ maintaining w >= 0;\n" +
				"		//@ maintaining z+(x*y*w) == x*y*y;\n" +
				"		while (w > 0) {\n" +
				"			z += u;\n" +
				"			w--;\n" +
				"			//@ assert z+(x*y*w) == x*y*y;\n" +
				"		}\n" +
				"		return z;\n" +
				"	}\n" +
				"	//@ requires x > 0;\n" +
				"	//@ ensures  \\result == x * x * x;\n" +
				"	public int m_25_cube(int x) {\n" +
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
				"			c--;\n" +
				"		}\n" +
				"		//@ assert z == x * x * x;\n" +
				"		return z;\n" +
				"	}\n" +
				"   public void m6m(int i) {\n" +
				"      int c = 5;\n" +
				"      int factorial = c;\n" +
				"      while (--c > 1)\n" +
				"            factorial *= c;\n" +
				"      //@ assert false;\n" +
				"   }\n" +
				"   //@ requires b >= 0;\n" +
				"   //@ ensures  \\result == a + b;\n" +
				"   public int sum1c2a(final int a, final int b) {\n" +
				"      int sum = a;\n" +
				"      int i = b;\n" +
				"      //@ maintaining sum == a + b - i;\n" +
				"      //@ maintaining i >= 0;\n" +
				"      //@ decreasing i+1;\n" +
				"      while (true) {\n" +
				"         //@ assert i >= 0;\n" +
				"         int var = i;\n" +
				"         if (!(i > 0)) {\n" +
				"            //@ assert i == 0;\n" +
				"            break;\n" +
				"         }\n" +
				"         sum++;\n" +
				"         i--;\n" +
				"         //@ assert i < var;\n" +
				"         //@ assert sum == a + b - i;\n" +
				"      }\n" +
				"      //@ assert i == 0;\n" +
				"      //@ assert sum == a + b - i;\n" +
				"      //@ assert sum == a + b;\n" +
				"      return sum;\n" +
				"   }\n" +
				"   public void countDownWithSideEffect2o() {\n" +
				"	   int i = 10;\n" +
				"	   //@ assert i  >= 0;\n" +
				"	   //@ maintaining i  >= 0;\n" +
				"	   //@ decreasing i;\n" +
				"	   while (0 < --i) {\n" +
				"	   }\n" +
				"	   //@ assert i >= 0;\n" +
				"	   //@ assert i == 0;\n" +
				"   }\n" +
				"}\n"
				},
				"");
	}
}