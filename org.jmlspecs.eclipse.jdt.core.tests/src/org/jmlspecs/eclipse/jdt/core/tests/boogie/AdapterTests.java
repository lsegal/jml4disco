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
}
