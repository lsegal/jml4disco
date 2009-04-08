package org.jmlspecs.eclipse.jdt.core.tests.esc;


public class WhileTests extends EscTest {
	public WhileTests(String name) {
		super(name);
	}

	public void test_000_assertFalse() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + "}\n" 
				},
				"----------\n" + 
				"1. ERROR in "+testsPath+"X.java (at line 4)\n" + 
				"	//@ assert false;\n" +
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}

	public void test_170_while() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
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
				"}\n"}, 
				"----------\n" + 
				"1. ERROR in "+testsPath+"X.java (at line 13)\n" + 
				"	//@ ensures  \\result != 0;\n" + 
				"	             ^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Postcondition).\n" + 
				"----------\n" + 
				"2. ERROR in "+testsPath+"X.java (at line 22)\n" + 
				"	//@ ensures  \\result != 0;\n" + 
				"	             ^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Postcondition).\n" + 
				"----------\n" + 
				"3. ERROR in "+testsPath+"X.java (at line 25)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"4. ERROR in "+testsPath+"X.java (at line 26)\n" + 
				"	//@ loop_invariant 0 <= x;\n" + 
				"	                   ^^^^^^\n" + 
				"Possible assertion failure (LoopInvariant).\n" + 
				"----------\n"
		);
	}

	public void test_170_while_m1() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result == 0;\n" +
				"   public int m1(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"}\n"}, 
				""
		);
	}
	public void test_170_while_m2() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result != 0;\n" +
				"   public int m2(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"}\n"}, 
				"----------\n" + 
				"1. ERROR in "+testsPath+"X.java (at line 4)\n" + 
				"	//@ ensures  \\result != 0;\n" + 
				"	             ^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Postcondition).\n" + 
				"----------\n"
		);
	}
	public void test_170_while_m3() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
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
				"}\n"}, 
				"----------\n" + 
				"1. ERROR in "+testsPath+"X.java (at line 4)\n" + 
				"	//@ ensures  \\result != 0;\n" + 
				"	             ^^^^^^^^^^^^\n" + 
				"Possible assertion failure (Postcondition).\n" + 
				"----------\n" + 
				"2. ERROR in "+testsPath+"X.java (at line 7)\n" + 
				"	//@ assert false;\n" + 
				"	           ^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in "+testsPath+"X.java (at line 8)\n" + 
				"	//@ loop_invariant 0 <= x;\n" + 
				"	                   ^^^^^^\n" + 
				"Possible assertion failure (LoopInvariant).\n" + 
				"----------\n"
		);
	}
//	"   public int find(int[] a, boolean[] b)\n" +
//	"   {\n" +
//	"      //@ assume a != null && b != null;\n" +
//	"      //@ assume a.length == b.length;\n" +
//	"      int spot = a.length;\n" +
//	"      //@ loop_invariant spot == a.length || (b[spot] && sport < i);\n" +
//	"      for (int i=0; i < a.length; i++) {\n" +
//	"            if (spot == a.length && a[i] != 0);\n" +
//	"               spot = i;\n" +
//	"            b[i] = (a[i] != 0);\n" +
//	"      }\n" +
//	"      int result = spot;\n" +
//	"      //@ assert (result == a.length) || b[result];\n" +
//	"      return result;\n" +
//	"   }\n" +
	public void test_175_whileBreak() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m(boolean b, boolean p) {\n" +
				"      while (b) {\n" +
				"            if (p) {\n" +
				"               break;\n" +
				"            }\n" +
				"      }\n" +
				"   }\n" +
				"  //@ requires i;\n" +
				"  public void m_break_2(boolean b, boolean i) {\n" +
				"      if (b) {\n" +
				"          //@ loop_invariant i;\n" +
				"          while (b) {\n" +
				"              //@ assert b & i;\n" +
				"              break;\n" +
				"          }\n" +
				"      }\n" +
				"  }\n" +
				"  //@ requires i & j;\n" +
				"  //@ ensures  b & i & j;\n" +
				"  public void m_break_3(boolean b, boolean i, boolean j) {\n" +
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
				"  //@ requires i & j;\n" +
				"  public void m_break_4(boolean b, boolean i, boolean j) {\n" +
				"      if (b) {\n" +
				"          //@ loop_invariant i;\n" +
				"          while (b) {\n" +
				"              //@ assert b & i & j;\n" +
				"              break;\n" +
				"          }\n" +
				"      }\n" +
				"  }\n" +
				"  //@ requires 100 <= y;\n" +
				"  public static int m4(int y) {\n" +
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
				"  public void m_break_1(boolean b, boolean i, boolean j) {\n" +
				"      //@ loop_invariant i;\n" +
				"      while (b) {\n" +
				"          //@ assert b;\n" +
				"          //@ assert i;\n" +
				"          //@ assert j;\n" +
				"          break;\n" +
				"      }\n" +
				"  }\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in "+testsPath+"X.java (at line 31)\n" +
				"	//@ assert b & i & j; // we don't know b\n" +
				"	           ^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n" +
				"2. ERROR in "+testsPath+"X.java (at line 55)\n" +
				"	//@ assert false; // here\n" +
				"	           ^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n" +
				"3. ERROR in "+testsPath+"X.java (at line 59)\n" +
				"	//@ ensures  i & j & b;\n" +
				"	                     ^\n" +
				"Possible assertion failure (Postcondition).\n" +
				"----------\n");
	}
	public void test_176_moreBreak() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"	//@ requires j;\n" +
				"   public static void m_while_1(boolean b, boolean j) {\n" +
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
				"   public static void m_while_2(boolean b, boolean j) {\n" +
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
				"}\n"
				},
				"----------\n" +
				"1. ERROR in "+testsPath+"X.java (at line 15)\n" +
				"	//@ assert j;\n" +
				"	           ^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n");
	}

	public void test_180_whileSideEffectCond() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public static void m0() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 0;\n" +
				"		while (i > 0) {\n" +
				"             i--;\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"	}\n" +
				"   public static void m1() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i > 0;\n" +
				"		while (--i > 0) {\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"	}\n" +
				"   public static void m2() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 3;\n" +
				"		while (i-- > 3) {\n" +
				"		}\n" +
				"		//@ assert i == 2;\n" +
				"	}\n" +
				"   public static void m3() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 0;\n" +
				"		while (--i > 0) {\n" +
				"		}\n" +
				"		//@ assert i == 4;\n" +
				"	}\n" +
				"   public static void m4() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 0;\n" +
				"		while (i-- > 1) {\n" +
				"		}\n" +
				"		//@ assert i == 1;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in "+testsPath+"X.java (at line 30)\n" +
				"	//@ assert i == 4;\n" +
				"	           ^^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n" +
				"2. ERROR in "+testsPath+"X.java (at line 37)\n" +
				"	//@ assert i == 1;\n" +
				"	           ^^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n");
	}

	public void test_190_whileVariant() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public static void m1() {\n" +
				"		int a = 10;\n" +
				"		//@ decreases a;\n" +
				"		while (a > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m2() {\n" +
				"		int b = 10;\n" +
				"		//@ decreases b;\n" +
				"		while (b > 0) {\n" +
				"             b--;\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m3() {\n" +
				"		int c = 10;\n" +
				"		//@ decreases c;\n" +
				"		while (c > 0) {\n" +
				"             c++;\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m4() {\n" +
				"		int d = 10;\n" +
				"		//@ decreases d;\n" +
				"		while (--d > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m5() {\n" +
				"		int e = 10;\n" +
				"		//@ decreases e;\n" +
				"		while (++e > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m6() {\n" +
				"		int f = 10;\n" +
				"		//@ decreases f;\n" +
				"		while (f-- > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m7() {\n" +
				"		int g = 10;\n" +
				"		//@ decreases g;\n" +
				"		while (g++ > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m8(boolean b) {\n" +
				"		int h = 10;\n" +
				"		//@ decreases h;\n" +
				"		while (h > 0) {\n" +
				"             if (b) {\n" +
				"                h--;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m9() {\n" +
				"		int i = 10;\n" +
				"		boolean b = true;\n" +
				"		//@ decreases i;\n" +
				"		while (i > 0) {\n" +
				"             if (b) {\n" +
				"                i--;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in "+testsPath+"X.java (at line 5)\n" +
				"	//@ decreases a;\n" +
				"	              ^\n" +
				"Possible assertion failure (LoopVariant).\n" +
				"----------\n" +
				"2. ERROR in "+testsPath+"X.java (at line 18)\n" +
				"	//@ decreases c;\n" +
				"	              ^\n" +
				"Possible assertion failure (LoopVariant).\n" +
				"----------\n" +
				"3. ERROR in "+testsPath+"X.java (at line 31)\n" +
				"	//@ decreases e;\n" +
				"	              ^\n" +
				"Possible assertion failure (LoopVariant).\n" +
				"----------\n" +
				"4. ERROR in "+testsPath+"X.java (at line 43)\n" +
				"	//@ decreases g;\n" +
				"	              ^\n" +
				"Possible assertion failure (LoopVariant).\n" +
				"----------\n" +
				"5. ERROR in "+testsPath+"X.java (at line 49)\n" +
				"	//@ decreases h;\n" +
				"	              ^\n" +
				"Possible assertion failure (LoopVariant).\n" +
				"----------\n");
	}
	public void test_195_whileContinueVariant() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public static void m1(boolean b) {\n" +
				"		int i = 10;\n" +
				"		//@ decreases i;\n" +
				"		while (i > 0) {\n" +
				"             if (b) {\n" +
				"                i--;\n" +
				"                continue;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"   public static void m2() {\n" +
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
				"}\n"
				},
				"----------\n" +
				"1. ERROR in "+testsPath+"X.java (at line 5)\n" +
				"	//@ decreases i;\n" +
				"	              ^\n" +
				"Possible assertion failure (LoopVariant).\n" +
				"----------\n");
	}
	public void test_196_whileContinueVariant() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
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
				"}\n"
				},
				"");
	}
	public void test_197_while_variantSideEffects() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
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
				"}\n"
				},
				"");
	}
	public void test_210_postfixInCondition() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"	public int m1() {\n" +
				"		int m=10;\n" +
				"		//@ maintaining m >= 0;\n" +
				"		while (m > 0) {\n" +
				"		      m = m - 1;\n" +
				"		}\n" +
				"		//@ assert m == 0;\n" +
				"		return m;\n" +
				"	}\n" +
				"	public int m2() {\n" +
				"		int m=10;\n" +
				"		//@ maintaining m >= 0;\n" +
				"		while (m-- > 1) {\n" +
				"		}\n" +
				"		//@ assert m == 0;\n" +
				"		return m;\n" +
				"	}\n" +
				"	public int m3() {\n" +
				"		int m=10;\n" +
				"		//@ maintaining m >= 0;\n" +
				"		while (m-- > 2) {\n" +
				"		}\n" +
				"		//@ assert m == 0;\n" +
				"		//@ assert false;\n" +
				"		return m;\n" +
				"	}\n" +
				"}\n" 
				},
				"----------\n" +
				"1. ERROR in "+testsPath+"X.java (at line 17)\n" +
				"	//@ assert m == 0;\n" +
				"	           ^^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n" +
				"2. ERROR in "+testsPath+"X.java (at line 25)\n" +
				"	//@ assert m == 0;\n" +
				"	           ^^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n" +
				"3. ERROR in "+testsPath+"X.java (at line 26)\n" +
				"	//@ assert false;\n" +
				"	           ^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n");
	}
	public void test_301_break() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"	//@ requires j;\n" +
				"   public static void m1(boolean b, boolean j) {\n" +
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
				"}\n" 
				},
				"");
	}
	public void test_302_break() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"	//@ requires j;\n" +
				"   public static void m1(boolean b, boolean j) {\n" +
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
				"}\n" 
				},
				"----------\n" + 
				"1. ERROR in "+testsPath+"X.java (at line 14)\n" +
				"	//@ assert b;\n" +
				"	           ^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n");
	}
	public void test_303_break() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   //@ requires j;\n" +
				"   public static void m2(boolean b, boolean j) {\n" +
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
				"}\n" 
				},
				"----------\n" + 
				"1. ERROR in "+testsPath+"X.java (at line 15)\n" +
				"	//@ assert b;\n" + 
				"	           ^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n");
	}

	public void test_1001_22comp() {
		this.runNegativeTest(new String[] {
				testsPath + "Comp22.java",
				"package tests.esc;\n" +
				"public class Comp22 {\n" +
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
				"}\n" 
				},
				"");
	}
	public void test_1002_23diff() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
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
				"}\n" 
				},
				"");
	}
	public void test_1003_24aTimes() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
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
				"}\n" 
				},
				"");
	}
	public void test_1004_24power() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
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
				"}\n" 
				},
				"");
	}
	public void test_1005_25cube() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
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
				"}\n" 
				},
				"");
	}
	public void test_9000_preDecInCondition() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m6(int i) {\n" +
				"      int c = 5;\n" +
				"      int factorial = c;\n" +
				"      while (--c > 1)\n" +
				"            factorial *= c;\n" +
				"      //@ assert false;\n" +
				"   }\n" +
				"}\n" 
				},
				"----------\n" +
				"1. ERROR in "+testsPath+"X.java (at line 8)\n" +
				"	//@ assert false;\n" +
				"	           ^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n");
	}
	public void test_9001_variant() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
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
				"}\n" 
				},
				"");
	}
	public void test_9002_countDownWithSideEffect() {
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void countDownWithSideEffect2() {\n" +
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
				"----------\n" +
				"1. ERROR in "+testsPath+"X.java (at line 10)\n" +
				"	//@ assert i >= 0;\n" +
				"	           ^^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n" +
				"2. ERROR in "+testsPath+"X.java (at line 11)\n" +
				"	//@ assert i == 0;\n" +
				"	           ^^^^^^\n" +
				"Possible assertion failure (Assert).\n" +
				"----------\n");
	}
}