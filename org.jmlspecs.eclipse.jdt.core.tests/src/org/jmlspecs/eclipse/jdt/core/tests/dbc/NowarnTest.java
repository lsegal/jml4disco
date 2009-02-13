package org.jmlspecs.eclipse.jdt.core.tests.dbc;
import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class NowarnTest extends AbstractRegressionTest {

	public final String workspace = "..";
	public final String path2jml4runtime = workspace + "/org.jmlspecs.jml4.runtime/bin";

    public NowarnTest(String name) {
        super(name);
    }
    
	protected String[] getDefaultClassPaths() {
		final String [] superDefaultClassPaths = super.getDefaultClassPaths();
		final int length = superDefaultClassPaths.length;
	    String[] defaultClassPaths = new String[length + 1];
        System.arraycopy(superDefaultClassPaths, 0, defaultClassPaths, 0, length);
        defaultClassPaths[length] = path2jml4runtime;
        return defaultClassPaths;
   }

    // Augment problem detection settings
    @SuppressWarnings("unchecked")
    protected Map<String, String> getCompilerOptions() {
        Map<String, String> options = super.getCompilerOptions();
        
        options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
        options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
        options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NON_NULL);
        options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.DISABLED);
        options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.IGNORE);
        options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.IGNORE);
        options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
        options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.IGNORE);
        options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
        options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
        options.put(CompilerOptions.OPTION_ReportNonStaticAccessToStatic, CompilerOptions.IGNORE);
        options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
        options.put(JmlCompilerOptions.OPTION_SpecPath, DbcTestCompiler.getSpecPath());
        options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.VERSION_1_6);
        options.put(CompilerOptions.OPTION_Source, CompilerOptions.VERSION_1_6);

        return options;
    }
        
    public void test_NowarnOk() {
      runNegativeTest(
          new String[] {
            "NowarnOkTest.java",
            "public class NowarnOkTest {\n" +
            "   void m1() {} //@ nowarn;\n" +
            "   void m2() {} //@ nowarn Cast;\n" +
            "   void m3() {} //@ nowarn IndexNegative, IndexTooBig;\n" +
            "}\n"
          },
          "");
    }
	public void test_NowarnErrorNoSemicolon() {
	  runNegativeTest(
	      new String[] {
	        "NowarnErrorNoSemicolon.java",
	        "public class NowarnErrorNoSemicolon {\n" +
	        "	// forgetting ';'\n" +
	        "   void m1() {} //@ nowarn Cast\n" +
	        "}\n"
	      },
			"----------\n" + 
			"1. ERROR in NowarnErrorNoSemicolon.java (at line 3)\n" + 
			"	void m1() {} //@ nowarn Cast\n" + 
			"}\n" + 
			"\n" + 
			"	                  ^^^^^^^^^^^^^\n" + 
			"invalid nowarn syntax\n" + 
			"----------\n"
	  		);
	}
}

