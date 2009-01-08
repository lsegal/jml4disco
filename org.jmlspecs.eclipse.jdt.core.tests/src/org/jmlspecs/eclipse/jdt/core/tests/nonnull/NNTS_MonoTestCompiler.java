package org.jmlspecs.eclipse.jdt.core.tests.nonnull;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class NNTS_MonoTestCompiler extends AbstractRegressionTest {

	public NNTS_MonoTestCompiler(String name) { 
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
	    return options;
	}

	public void test_0001_fieldInit() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   /*@mono_non_null*/ String f1 = \"hello\";\n" +
                "   /*@mono_non_null*/ String f2 = null;\n" +
                "   /*@nullable*/      String n1 = \"world\";\n" +
                "   /*@mono_non_null*/ String f3 = n1;\n" +
                "}\n"}, 
            "----------\n" +
            "1. ERROR in X.java (at line 3)\n" +
            "	/*@mono_non_null*/ String f2 = null;\n" +
            "	                          ^^\n" +
            "Possible assignment of null to an L-value declared non_null\n" +
            "----------\n" +
            "2. ERROR in X.java (at line 5)\n" +
            "	/*@mono_non_null*/ String f3 = n1;\n" +
            "	                          ^^\n" +
            "Possible assignment of null to an L-value declared non_null\n" +
            "----------\n" );
	}
	public void test_0001_fieldAssign() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   /*@mono_non_null*/ String f1;\n" +
                "   /*@mono_non_null*/ String f2;\n" +
                "   /*@nullable*/      String n1;\n" +
                "   /*@mono_non_null*/ String f3;\n" +
                "   void m() {\n" +
                "      f1 = \"world\";\n" +
                "      f2 = null;\n" +
                "      f3 = n1;\n" +
                "   }\n" +
                "}\n"}, 
            "----------\n" +
            "1. ERROR in X.java (at line 8)\n" +
            "	f2 = null;\n" +
            "	^^^^^^^^^\n" +
            "Possible assignment of null to an L-value declared non_null\n" +
            "----------\n" +
            "2. ERROR in X.java (at line 9)\n" +
            "	f3 = n1;\n" +
            "	^^^^^^^\n" +
            "Possible assignment of null to an L-value declared non_null\n" +
            "----------\n" );
	}
}