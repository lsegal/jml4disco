package org.jmlspecs.eclipse.jdt.core.tests.boogie;

import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.core.tests.compiler.regression.Requestor;
import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.batch.CompilationUnit;
import org.eclipse.jdt.internal.compiler.env.ICompilationUnit;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.boogie.BoogieVisitor;
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
	
	CompilationUnitDeclaration compileToAst(String source) {
		CompilerOptions compilerOptions = new CompilerOptions(getCompilerOptions());
		Requestor requestor = new Requestor( /* custom requestor */
						false,
						null /* no custom requestor */,
						false,
						false);
		Compiler compiler = 
				new Compiler(
					getNameEnvironment(new String[]{}, null /* no class libraries */), 
					getErrorHandlingPolicy(), 
					compilerOptions,
					requestor, 
					getProblemFactory()) { 
			public void compile(ICompilationUnit[] sourceUnits) {
				parseThreshold = sourceUnits.length + 1;
				beginToCompile(sourceUnits);
			}
		};

		CompilationUnit cUnit = new CompilationUnit(source.toCharArray(), "test.java", null);
		compiler.compile(new CompilationUnit[] { cUnit });
		return compiler.unitsToProcess[0];
	}
	
	protected void compareJavaToBoogie(String java, String boogie) {
		CompilationUnitDeclaration unit = compileToAst(java);
		BoogieVisitor visitor = new BoogieVisitor();
		unit.traverse(visitor, unit.scope);
		assertEquals(boogie, visitor.getResults());
	}

	protected void compareJavaExprToBoogie(String java, String boogie) {
		CompilationUnitDeclaration unit = compileToAst("public class A { static { return " + java + "; } }");
		BoogieVisitor visitor = new BoogieVisitor();
		unit.traverse(visitor, unit.scope);
		
		String results = visitor.getResults();
		Pattern p = Pattern.compile(".+return (.+);.+", Pattern.DOTALL | Pattern.MULTILINE);
		Matcher m = p.matcher(results);
		if (m.matches()) {
			results = m.group(1);
			assertEquals(boogie, results);
		}
		else {
			fail("Invalid expression");
		}
	}
	
	public void testFalseLiteral() {
		compareJavaExprToBoogie("false", "false");
	}

	public void testTrueLiteral() {
		compareJavaExprToBoogie("true", "true");
	}

	public void testIntLiteral() {
		compareJavaExprToBoogie("2", "2");
	}
	
	public void testDoubleLiteral() {
		compareJavaExprToBoogie("2.2456", "2.2456");
	}
	

	public void testMethodDefinition() {
		this.compareJavaToBoogie(
			// java
			"package tests.esc;\n" + 
			"public class A {\n" +
			"   public void m() {\n" + 
			"   	//@ assert false;\n" + 
			"   }\n" +
			"	" +
			"	public int n() {\n" +
			"		//@ assert true;" +
			"	}\n" + 
			"}\n"
			,
			// expected boogie
			"procedure tests.esc.A.m() {\n" +
			"	assert false;\n" +
			"}\n" +
			"procedure tests.esc.A.n() returns (__result__ : int) {\n" +
			"	assert true;\n" +
			"}\n"
		);
	}
	

/*******************************************
*			ASSERTS
*******************************************/	
	public void test_001_assertFalse() {
		this.runNegativeTest(new String[] {
				testsPath + "A.java", // filename
				"package tests.esc;\n" + //java source
				"public class A {\n" +
				"   public void m() {\n" + 
				"   	//@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				},
				""); // javac output
	}

	public void test_002_assertFalse() {
		this.runNegativeTest(new String[] {
				testsPath + "A.java", // filename
				"package tests.esc;\n" + //java source
				"public class A {\n" +
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
				""); // javac output
	}
	public void test_003_assertParam() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m(boolean b) {\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 
				"}\n" 
				,
				// expected boogie
				"procedure tests.esc.X.m(b : bool) {\n" +
				"	assert b;\n" +
				"}\n" 			
				);
	}	
	
	public void test_004_assert_sequence_and() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert false && false;\n" + 
				"   }\n" +
				"}\n"		
				,
				// expected boogie
				"procedure tests.esc.X.m1() {\n" +
				"	assert false && false;\n" +
				"}\n"
				
				);
	}
	
	public void test_005_assert_sequence_or() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert false || false;\n" + 
				"   }\n" + 				
				"}\n"
				,				
				// expected boogie
				"procedure tests.esc.X.m1() {\n" +
				"	assert false || false;\n" +
				"}\n"
				);
	}	
			
	public void test_006_assert_sequence_and_or() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m1() {\n" + 
				"      //@ assert false && (false || false);\n" + 
				"   }\n" + 		
				"}\n"
				,
				//expected boogie
				"procedure tests.esc.X.m1() {\n" +
				"	assert false && (false || false);\n" +
				"}\n"				
				);
	}	
	
	public void test_007_assert_sequence_or_and() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m2() {\n" + 
				"      //@ assert (false || false) && false;\n" + 
				"   }\n" + 			
				"}\n"
				,
				//expected boogie
				"procedure tests.esc.X.m1() {\n" +
				"	assert (false || false) && false ;\n" +
				"}\n"
				);
	}

	public void test_008_assert_sequence_tt() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assert true;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				,
				//expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assert true;\n" +
				"	assert true;\n" +				
				"}\n"
				);
	}	
	public void test_009_assert_sequence_tf() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assert true;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				,
				//expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assert true;\n" +
				"	assert false;\n" +				
				"}\n"
				);
	}
	public void test_007_assert_sequence_ft() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assert false;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				,
				//expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assert false;\n" +
				"	assert true;\n" +				
				"}\n"
				);
	}
	public void test_008_assert_sequence_ff() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assert false;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				,
				//expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assert false;\n" +
				"	assert false;\n" +				
				"}\n"
				);
	}	
	
		
/*******************************************
*			ASSUMES
*******************************************/
		
	public void test_0100_assumeFalse() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assume false;\n" + 
				"   }\n" + 
				"}\n"
				,
				// expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assume false;\n" +
				"}\n" 				
				);
	}	
	public void test_0101_assumeTrue() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assume true;\n" + 
				"   }\n" + 
				"}\n" 
				,
				// expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assume true;\n" +
				"}\n" 				
				);
	}

	public void test_0200_sequence_assume_assert_tt() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assume true;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				,
				// expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assume true;\n" +
				"	assert true;\n" +
				"}\n"
				);
	}
	public void test_0201_sequence_assume_assert_ff() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assume false;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				,
				// expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assume false;\n" +
				"	assert false;\n" +
				"}\n"
				);
	}	
	public void test_0203_sequence_assume_assert_ft() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assume false;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"}\n" 
				,
				// expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assume false;\n" +
				"	assert true;\n" +
				"}\n"
				);
	}	
	public void test_0204_sequence_assume_assert_tf() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
				"   public void m() {\n" + 
				"      //@ assume true;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"}\n" 
				,
				// expected boogie
				"procedure tests.esc.X.m() {\n" +
				"	assume true;\n" +
				"	assert false;\n" +
				"}\n"
				);
	}	

	public void test_0300_IfCondition() {
		compareJavaToBoogie(	
			// java source
			"package tests.esc;\n" + 
			"public class A {\n" +
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
			, 
			// TODO expected boogie
			"procedure tests.esc.A.m(x: int, y: int) returns (__result__ : java.lang.String) {\n" +
			"	var z : int;\n" +
			"	z := 3;\n" +
			"	if (x == 1) {\n" +
			"		return string_lit_97;\n" +
			"	}\n" +
			"	else {\n" +
			"		return string_lit_98;\n" +
			"	}\n" +
			"}\n"
		);
	}
	public void test_0301_IfCondition_ternary() {
		this.compareJavaToBoogie(
				"package tests.esc;\n" +
				"public class X {\n" + 
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
				,
				//TODO expected boogie
				""
				);
	}
	public void test_0302_int_eq() {
		this.compareJavaToBoogie(
				//java
				"package tests.esc;\n" +
				"public class X {\n" + 
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
				,
				//TODO expected Boogie
				""
				);
	}
	
	public void test_0303_int_arith() {
		this.compareJavaToBoogie(	
				//java
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
				, 
				// TODO expected boogie
				""
				);			
		}

	public void test_0304_arith_cond() {
		this.compareJavaToBoogie(
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
				, 
				//TODO expected boogie
				""
				);
		}
	public void test_0305_boolExpr_cond() {
		this.compareJavaToBoogie(
				//java
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
				, 
				// TODO expected boogie
				""
				);
	}

	public void test_0306_implies() {
		this.compareJavaToBoogie(
				//java
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
				,
				//TODO expected boogie
				""
				);
		}

}
