package org.jmlspecs.eclipse.jdt.core.tests.esc;


public class FieldTests extends EscTest {
	public FieldTests(String name) {
		super(name);
	}

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