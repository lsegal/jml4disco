package org.jmlspecs.eclipse.jdt.core.tests.boogie;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.PostProcessor;

public class AdapterTests extends AbstractRegressionTest {
	public AdapterTests(String name) {
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
		options.put(JmlCompilerOptions.OPTION_EnableJmlBoogie, CompilerOptions.ENABLED);
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

	// term=JmlAssertStatement
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
				"This assertion might not hold.\n" + 
				"----------\n");
	}
    
	// term=JmlAssertStatement
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
	
	// term=MethodDeclaration,JmlAssertStatement,Argument
	public void test_003_assertParam() {
		this.runNegativeTest (new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m(boolean b) {\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 
				"}\n" 
		 		},
				"----------\n" + 
				"1. ERROR in " + testsPath + "X.java (at line 4)\n" + 
				"	//@ assert b;\n" +
				"	           ^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n");
	}
	
	// term=JmlAssertStatement,OR_OR_Expression	 
	public void test_004_assert_sequence_and() {
		this.runNegativeTest (new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assert false && false;\n" + 
				"   }\n" +
				"}\n"		
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "X.java (at line 4)\n" + 
				"	//@ assert false && false;\n" +
				"	           ^^^^^^^^^^^^^^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n");
	}
	
	// term=JmlAssertStatement,AND_AND_Expression,OR_OR_Expression
	public void test_006_assert_sequence_and_or() {
		this.runNegativeTest (new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert false && (false || false);\n" + 
				"   }\n" + 		
				"}\n"
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "X.java (at line 4)\n" + 
				"	//@ assert false && (false || false);\n" +
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n");
	}

	// term=JmlAssertStatement,AND_AND_Expression,OR_OR_Expression
	public void test_007_assert_sequence_or_and() {
		this.runNegativeTest (new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +				
				"   public void m1() {\n" + 
				"      //@ assert (false || false) && false;\n" + 
				"   }\n" + 			
				"}\n"
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "X.java (at line 4)\n" + 
				"	//@ assert (false || false) && false;\n" +
				"	           ^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n");
	}	
	// term=JmlAssertStatement
	public void test_008_assert_sequence_tt() {
		this.runNegativeTest (new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +		
				"   public void m() {\n" + 
				"      //@ assert true;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}	
	
	// term=JmlAssertStatement
	public void test_009_assert_sequence_tf() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assert true;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "X.java (at line 5)\n" + 
				"	//@ assert false;\n" +
				"	           ^^^^^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n");
	}	
	
	// term=JmlAssertStatement
	public void test_007_assert_sequence_ft() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assert false;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "X.java (at line 4)\n" + 
				"	//@ assert false;\n" +
				"	           ^^^^^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n");
	}
	
	// term=JmlAssertStatement
	public void test_008_assert_sequence_ff() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assert false;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "X.java (at line 4)\n" + 
				"	//@ assert false;\n" +
				"	           ^^^^^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n");
	}
	
	// term=AssertStatement
	public void test_009_JavaAssertFalse() {
		this.runNegativeTest(new String[] {
				testsPath + "A.java",
				"package tests.esc;\n" +
				"public class A {\n" +
				"   public void m() {\n" + 
				"      assert false;\n" + 
				"   }\n" + "}\n" 
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "A.java (at line 4)\n" + 
				"	assert false;\n" +
				"	       ^^^^^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n");
	}
    
	// term=AssertStatement
	public void test_010_JavaAssertTrue() {
		this.runNegativeTest(new String[] {
				testsPath + "B.java",
				"package tests.esc;\n" +
				"public class B {\n" + 
				"   public void m() {\n" + 
				"      assert true: 12345;\n" + 
				"   }\n" + 
				"}\n" 
				}, 
				"");
	}

	// term=JmlAssumeStatement    
	public void test_0100_assumeFalse() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assume false;\n" + 
				"   }\n" + 
				"}\n"
				},
				"");
	}		

	// term=JmlAssumeStatement
	public void test_0101_assumeTrue() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assume true;\n" + 
				"   }\n" + 
				"}\n"
				},
				"");
	}
	
	// term=MethodDeclaration
	public void test_0110_MethodDeclaration_EmptyMethod() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m1() {\n" +
				"      \n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}	
	
	// term=MethodDeclaration,Argument,JmlResultReference,JmlMethodSpecification,ReturnStatement,JmlAssertStatement
	public void test_0111_MethodDefinition() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"   	//@ assert false;\n" + 
				"   }\n" +
				"	" +
				"   //@ ensures \\result == 42;\n" + 
				"	public int n() {\n" +
				"		//@ assert true;\n" +
				"		return 42;\n" +
				"	}\n" + 
				"}\n"	
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "X.java (at line 4)\n" + 
				"	//@ assert false;\n" +
				"	           ^^^^^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n");
	}
	// term=MethodDeclaration,JmlAssertStatement
	public void test_0112_DoubleMethodDefinition() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"   	//@ assert false;\n" + 
				"   }\n" +
				"	" +
				"	public void n() {\n" +
				"		//@ assert false;\n" +
				"	}\n" + 
				"}\n"	
				},
				"----------\n" +
				"1. ERROR in " + testsPath + "X.java (at line 4)\n" +
				"	//@ assert false;\n" +
				"	           ^^^^^\n" +
				"----------\n" +
				"2. ERROR in " + testsPath + "X.java (at line 7)\n" +
				"	//@ assert false;\n" +
				"	           ^^^^^\n" +
				"----------\n");
	}
	
	// term=JmlAssumeStatement,JmlAssertStatement
	public void test_0200_sequence_assume_assert_tt() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assume true;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}	
	
	// term=JmlAssumeStatement	
	public void test_0201_sequence_assume_assert_ff() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assume false;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}	
	
	// term=JmlAssumeStatement
	public void test_0202_sequence_assume_assert_ft() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assume true;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"----------\n" +
				"1. ERROR in " + testsPath + "X.java (at line 5)\n" +
				"	//@ assert false;\n" +
				"	           ^^^^^\n" +
				"This assertion might not hold.\n" +
				"----------\n"
			);
	}
	
	// term=JmlAssumeStatement
	public void test_0203_sequence_assume_assert_tf() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m() {\n" + 
				"      //@ assume false;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}	
	
	// term=IfStatement,Argument,ReturnStatement,StringLiteral
	public void test_0300_IfCondition() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public String m(int x, int y) {\n" +
				"		int z = 3;\n" + 
				"   	if (x == 1) {\n" +
				"			return \"a\";\n" +	
				"		}\n" + 
				"		else {\n" +
				"			return \"b\";\n" +
				"		}\n" +
				"   }\n" + 
				"}\n"
				},
				"");
	}
	
	// term=IfStatement
	public void test_0301_IfCondition_noBlock() {		 
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +
				"   public void m1() {\n" +
				"		if (true) \n" +
				"      		//@ assert (true);\n" +
				"   }\n" +
				"}\n" 
				},
				"");
	}	
	
	// term=WhileStatement
	public void test_350_while() {
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +	
				"   public void m1() {\n" +
				"      while (true == true) {" +
				"         //@ assert true;\n" +
				"      }\n" + 
				"   }\n" + 
				"}\n" 
				},
				"");
	}	
	
	// term=WhileStatement,BreakStatement,LabeledStatement
	public void test_0370_Break_withlabel() {		 
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +	
				"   public void m() {\n" +
				"		blah:\n" +
				"		while(true){\n" +
				"      		//@ assert (true);\n" +
				"			break blah;\n" +	
				"		}\n" +	
				"		if (true) \n" +
				"      		//@ assert (true);\n" +

				"   }\n" +
				"}\n" 
				},
				"");
	}
	
	// term=WhileStatement,BreakStatement
	public void test_0371_Break() {		 
		this.runNegativeTest (new String[] {				
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" +	
				"   public void m() {\n" +
				"		while(true){\n" +
				"      		//@ assert (true);\n" +
				"			break;\n" +	
				"		}\n" +
				"	}\n" +	
				"}\n" 
				},
				"");
	}

	// term=ReturnStatement,JmlMethodSpecification,EqualExpression,IntLiteral
	public void test_0400_postconditionFails() {
		this.runNegativeTest(new String[] {
				testsPath + "A.java",
				"package tests.esc;\n" +
				"public class A {\n" +
				"   //@ ensures \\result == 42;\n" + 
				"	public int n() {\n" +
				"		return 43;\n" +
				"	}\n" + 
				"}"
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "A.java (at line 3)\n" + 
				"	//@ ensures \\result == 42;\n" +
				"	    ^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"This postcondition might not hold.\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "A.java (at line 5)\n" + 
				"	return 43;\n" +
				"	       ^^\n" + 
				"This postcondition might not hold.\n" + 
				"----------\n");
	}

	// term=ReturnStatement,JmlAssertStatement,JmlMethodSpecification,EqualExpression,IntLiteral
	public void test_0400_MultipleFailures() {
		this.runNegativeTest(new String[] {
				testsPath + "A.java",
				"package tests.esc;\n" +
				"public class A {\n" +
				"	public void x() {\n" +
				"		//@ assert false;\n" +
				"	}\n" + 
				"\n" +
				"   //@ ensures \\result == 42;\n" + 
				"	public int n() {\n" +
				"		return 43;\n" +
				"	}\n" + 
				"}"
				},
				"----------\n" + 
				"1. ERROR in " + testsPath + "A.java (at line 4)\n" + 
				"	//@ assert false;\n" +
				"	           ^^^^^\n" + 
				"This assertion might not hold.\n" + 
				"----------\n" + 
				"2. ERROR in " + testsPath + "A.java (at line 7)\n" + 
				"	//@ ensures \\result == 42;\n" +
				"	    ^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"This postcondition might not hold.\n" + 
				"----------\n" + 
				"3. ERROR in " + testsPath + "A.java (at line 9)\n" + 
				"	return 43;\n" +
				"	       ^^\n" + 
				"This postcondition might not hold.\n" + 
				"----------\n");
	}
}