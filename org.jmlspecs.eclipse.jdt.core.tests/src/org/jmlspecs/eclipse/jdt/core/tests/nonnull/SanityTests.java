package org.jmlspecs.eclipse.jdt.core.tests.nonnull;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class SanityTests extends AbstractRegressionTest {
	public SanityTests(String name) { 
	    super(name);
	}

	// Augment problem detection settings
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
	    Map<String, String> options = super.getCompilerOptions();

	    options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NULLABLE);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.ERROR);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.ERROR);
		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_SpecPath, NullTypeSystemTestCompiler.getSpecPath());
		options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_Source, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_TargetPlatform, CompilerOptions.VERSION_1_5);
		return options;
	}
    public void test_001_Sanity() {
		this.runConformTest(
				new String[] {
					"X.java",
	                "public class X {\n" +
	                "}\n" });
    }
    public void test_002_Sanity_main() {
		this.runConformTest(
				new String[] {
					"X.java",
	                "public class X {\n" +
	                "   public static void main(String[] args) {\n" +
	                "   }\n" +
	                "}\n" });
    }
    public void test_003a_extends() {
		this.runConformTest(
				new String[] {
					"X.java",
	                "class X extends Object {\n" +
	                "}\n" });
    }
    public void test_003b_extends() {
		this.runConformTest(
				new String[] {
					"X.java",
	                "public class X extends Object {\n" +
	                "}\n" });
    }
    public void test_004a_implements() {
		this.runConformTest(
				new String[] {
					"X.java",
	                "class X implements Cloneable {\n" +
	                "}\n" });
    }
    public void test_004b_implements() {
		this.runConformTest(
				new String[] {
					"X.java",
	                "public class X implements Cloneable {\n" +
	                "}\n" });
    }
    public void test_005a_extends_implements() {
		this.runConformTest(
				new String[] {
					"X.java",
	                "class X extends Object implements Cloneable {\n" +
	                "}\n" });
    }
    public void test_005b_extends_implements() {
		this.runConformTest(
				new String[] {
					"X.java",
	                "public class X extends Object implements Cloneable {\n" +
	                "}\n" });
    }
    public void test_006_syntaxErrorEndClass() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" + 
					"	int m() {} \n" + 
					"	int m(int x y) {}\n" + 
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	int m() {} \n" +
				"	         ^\n" +
				"Syntax error, insert \"}\" to complete ClassBody\n" +
				"----------\n" +
				"2. ERROR in X.java (at line 3)\n" +
				"	int m(int x y) {}\n" +
				"	      ^^^\n" +
				"Syntax error on token \"int\", invalid Modifiers\n" +
				"----------\n" +
				"3. ERROR in X.java (at line 4)\n" +
				"	}\n" +
				"	^\n" +
				"Syntax error on token \"}\", delete this token\n" +
				"----------\n"
		);
    }
    public void test_007_varArgs() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" + 
					"	int m() {return 0;} \n" + 
					"	int m(int... y) {return 0;}\n" + 
					"}\n",
				},
				""
		);
    }
}
