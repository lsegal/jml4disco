package org.jmlspecs.eclipse.jdt.core.tests.esc;



public class ArrayTests extends EscTest {
	public ArrayTests(String name) {
		super(name);
	}

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