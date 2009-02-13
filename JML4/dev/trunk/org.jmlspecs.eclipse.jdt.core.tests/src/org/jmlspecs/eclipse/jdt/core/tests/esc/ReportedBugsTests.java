package org.jmlspecs.eclipse.jdt.core.tests.esc;


public class ReportedBugsTests extends EscTest {
	public ReportedBugsTests(String name) {
		super(name);
	}
	public void test_0001_internalException() {
		//reported by David Cok on Fri, May 30, 2008 at 10:16 PM
		this.runNegativeTest(new String[] {
				testsPath + "A.java",
				"package tests.esc;\n" +
				"\n" +
				"public class A {\n" +
				"\n" +
				"   /*@ requires x < 0; */\n" +
				"   /*@ ensures false;  */\n" +
				"   static public void mmm(int x) {\n" +
				"      /*@ assert x == 0 ; */\n" +
				"      q(x);\n" +
				"      //return true;\n" +
				"   }\n" +
				"\n" +
				"   //@ requires y > 0;\n" +
				"   static public int q(int y) {\n" +
				"      return y;\n" +
				"   }\n" +
				"\n" +
				"}\n" 
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "A.java (at line 6)\n" + 
				"	/*@ ensures false;  */\n" + 
				"	            ^^^^^\n" + 
				"Possible assertion failure (Postcondition).\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "A.java (at line 8)\n" + 
				"	/*@ assert x == 0 ; */\n" + 
				"	           ^^^^^^\n" + 
				"Possible assertion failure (Assert).\n" + 
				"----------\n" + 
				"3. ERROR in " + testsPath + "A.java (at line 13)\n" + 
				"	//@ requires y > 0;\n" + 
				"	             ^^^^^\n" + 
				"Possible assertion failure (Precondition).\n" + 
				"----------\n");
	}
	public void test_0002_missingSpec() {
		//reported by Sebastian Huber on Fri, Jan 9, 2009 at 10:49 AM
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"\n" +
				"public class X {\n" +
				"\n" +
				"   int compute(int p) {\n" +
				"      return 0;\n" +
				"   }\n" +
				"\n" +
				"   public void m(int v1) {\n" +
				"      X x = new X();\n" +
				"      int v2 = x.compute(v1); // <-- NullPointerException thrown\n" +
				"   }\n" +
				"\n" +
				"}\n" 
				},
				"");
	}
}