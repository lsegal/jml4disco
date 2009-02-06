package org.jmlspecs.eclipse.jdt.core.tests.esc.casestudy;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class FactorialTests extends AbstractRegressionTest {
    public FactorialTests(String name) {
        super(name);
    }

    public final String workspace = "..";
	public final String path2jml4runtime = workspace + "/org.jmlspecs.jml4.runtime/bin";
	protected String[] getDefaultClassPaths() {
		final String [] superDefaultClassPaths = super.getDefaultClassPaths();
		final int length = superDefaultClassPaths.length;
	    String[] defaultClassPaths = new String[length + 1];
        System.arraycopy(superDefaultClassPaths, 0, defaultClassPaths, 0, length);
        defaultClassPaths[length] = path2jml4runtime;
        return defaultClassPaths;
   }

    // Augment problem detection settings
    @Override
    @SuppressWarnings("unchecked")
    protected Map<String, String> getCompilerOptions() {
        Map<String, String> options = super.getCompilerOptions();

        options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
        options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
        options.put(JmlCompilerOptions.OPTION_EnableJmlEsc, CompilerOptions.ENABLED);
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

	private final String testsPath = "tests" + '\\' + "esc" + '\\' + "casestudy" + '\\' ;
	
    public void test_0001_factorial() {
        this.runNegativeTest(new String[] {
           testsPath + "Factorial.java",
           "package tests.esc.casestudy;\n" +
           "public class Factorial {\n" +
           "   //@ requires n >= 0;\n" +
           "   //@ ensures  \\result == (\\product int i; 1 <= i && i <= n ; i);\n" +
           "   public static int factorial(int n) {\n" +
           "      return (n == 0)\n" +
           "           ? 1\n" +
           "           : n * factorial(n - 1);\n" +
           "   }\n" +
           "\n" +
           "   //@ requires n >= 0;\n" +
           "   //@ ensures  \\result == (\\product int i; 1 <= i && i <= n ; i);\n" +
           "   public static int factorial_2(int n) {\n" +
           "      if (n == 0)\n" +
           "         return 1;\n" +
           "      return n * factorial(n - 1);\n" +
           "   }\n" +
           "\n" +
           "   //@ requires n >= 0;\n" +
           "   //@ ensures  \\result == (\\product int j; 1 <= j && j <= n ; j);\n" +
           "   public static int factorial_3(int n) {\n" +
           "      int result = 1;\n" +
           "      int i=1;\n" +
           "      //@ maintaining result == (\\product int j; 1 <= j && j <= i-1; j);\n" +
           "      //@ decreases   n-i+1;\n" +
           "      while (i <= n)\n" +
           "            result *= i++;\n" +
           "            return result;\n" +
           "   }\n" +
           "}\n"
        },
        "----------\n" +
        "----------\n");
    }

}
