package org.jmlspecs.eclipse.jdt.core.tests.esc.casestudy;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class EuclidTests extends AbstractRegressionTest {
    public EuclidTests(String name) {
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
	
    public void test_0001_divisor() {
        this.runNegativeTest(new String[] {
        		testsPath + "Euclid1.java",
				"package tests.esc.casestudy;\n" +
                "public class Euclid1 {\n" +
                "   //@ requires a >= 0 && b > 0;\n" +
                "   //@ ensures  \\result == (a % b == 0);\n" +
                "   public static boolean divides(int a, int b) {\n" +
                "      return (a - (a / b) * b) == 0;\n" +
                "   }\n" +
                "   public void testDivisor() {\n" +
                "   //@ assert divides(10, 5);\n" +
                "   //@ assert divides(10, 3);\n" +
                "   }\n" +
                "}\n"
                },
                "----------\n" +
        		"1. ERROR in tests\\esc\\casestudy\\Euclid1.java (at line 10)\n" + 
        		"	//@ assert divides(10, 3);\n" + 
        		"	           ^^^^^^^^^^^^^^\n" + 
        		"Possible assertion failure (Assert).\n" + 
        		"----------\n");
    }

    public void test_0002_isGcd_And() {
        this.runNegativeTest(new String[] {
				testsPath + "Euclid2And.java",
				"package tests.esc.casestudy;\n" +
                "public class Euclid2And {\n" +
                "   //@ requires a >= 0;\n" +
                "   //@ requires b > 0;\n" +
                "   //@ ensures  \\result == (a % b == 0);\n" +
                "   public static boolean divides(int a, int b) {\n" +
                "      return (a - (a/b)*b) == 0;\n" +
                "   }\n" +
                "   /*@ requires gcd > 0;\n" +
                "     @ requires a >= 0;\n" +
                "     @ requires b >= 0;\n" +
                "     @ ensures  \\result == (divides(a, gcd)\n" +
                "     @                  & divides(b, gcd)\n" +
                "     @                  & (\\forall int d; \n" +
                "     @                               0 < d & d <= a & d <= b;\n" +
                "     @                               (divides(a, d) & divides(b, d))\n" +
                "     @                               ==> d <= gcd));\n" +
                "     @*/\n" +
                "   public static boolean isGcd(int gcd, int a, int b) {\n" +
                "       if (! (divides(a, gcd) & divides(b, gcd)))\n" +
                "          return false;\n" +
                "       int i = 2;\n" +
                "       /*@ maintaining (\\forall int d; \n" +
                "         @                       1 < d & d <= i;\n" +
                "         @                       (divides(a, d) & divides(b, d))\n" +
                "         @                       ==> d <= gcd);\n" +
                "         @ maintaining 2 <= i & (a < 2 | i <= a+1);\n" +
                "         @ decreases a-i+2;" +
                "         @*/\n" +
                "       while (i <= a) {\n" +
                "             if (divides(a, i) & divides(b, i) & i > gcd)\n" +
                "                return false;\n" +
                "             i++;\n" +
                "       }\n" +
                "       return true;\n" +
                "   }\n" +
                "   public static void testIsGcd() {\n" +
                "      //@ assert isGcd( 6, 12, 18);\n" +
                "      //@ assert isGcd( 2,  4, 14);\n" +
                "      //@ assert isGcd(14, 42, 56);\n" +
                "      //@ assert isGcd(15, 42, 56);\n" +
                "   }\n" +
                "}\n"
                },
                "----------\n" +
        		"1. ERROR in tests\\esc\\casestudy\\Euclid2And.java (at line 36)\n" + 
        		"	//@ assert isGcd(15, 42, 56);\n" + 
        		"	           ^^^^^^^^^^^^^^^^^\n" + 
        		"Possible assertion failure (Assert).\n" + 
        		"----------\n");
    }

    // based on code from Wikipedia s.v. "Euclid's Algorithm"
    public void test_0100_Euclid() {
        this.runNegativeTest(new String[] {
        		testsPath + "Euclid100.java",
				"package tests.esc.casestudy;\n" +
                "public class Euclid100 {\n" +
                "   //@ requires a >= 0;\n" +
                "   //@ requires b > 0;\n" +
                "   //@ ensures  \\result == (a % b == 0);\n" +
                "   public static boolean divides(int a, int b) {\n" +
                "      return (a - (a/b)*b) == 0;\n" +
                "   }\n" +
                "   /*@ requires gcd > 0;\n" +
                "     @ requires a >= 0;\n" +
                "     @ requires b >= 0;\n" +
                "     @ ensures  \\result == (divides(a, gcd)\n" +
                "     @                  & divides(b, gcd)\n" +
                "     @                  & (\\forall int d; \n" +
                "     @                               0 < d & d <= a & d <= b;\n" +
                "     @                               (divides(a, d) & divides(b, d))\n" +
                "     @                               ==> d <= gcd));\n" +
                "     @*/\n" +
                "   public static boolean isGcd(int gcd, int a, int b) {\n" +
                "       if (! (divides(a, gcd) & divides(b, gcd)))\n" +
                "          return false;\n" +
                "       int i = 2;\n" +
                "       /*@ maintaining (\\forall int d; \n" +
                "         @                       1 < d & d <= i;\n" +
                "         @                       (divides(a, d) & divides(b, d))\n" +
                "         @                       ==> d <= gcd);\n" +
                "         @ maintaining 2 <= i & (a < 2 | i <= a+1);\n" +
                "         @ decreases a-i+2;" +
                "         @*/\n" +
                "       while (i <= a) {\n" +
                "             if (divides(a, i) & divides(b, i) & i > gcd)\n" +
                "                return false;\n" +
                "             i++;\n" +
                "       }\n" +
                "       return true;\n" +
                "   }\n" +
                "   //@ requires a >= 0 & b >= 0 & (b > 0 | a > 0);\n" +
                "   //@ ensures  \\result > 0 & isGcd(\\result, a, b);\n" +
                "   //@ pure\n" +
                "   public static int original_gcd(int a, int b) { \n" +
                "    	if (a == 0)\n" +
                "    		return b;\n" +
                "	    /*@ maintaining a >= 0 & b >= 0;" +
                "         @ maintaining (\\forall int k;\n" +
                "	      @                       0 < k & k <= a;\n" +
                "         @                       isGcd(k, a, b) == isGcd(k, \\old(a), \\old(b)));\n" +
                "	      @ decreases   a + b;\n" +
                "         @*/\n" +
                "	    while (b != 0) {\n" +
                "	    	if (a > b)\n" +
                "	    		a -= b;\n" +
                "	    	else\n" +
                "	    		b -= a;\n" +
                "	    }\n" +
                "	    return a;\n" +
                "   }\n" +
                "   public static void testOriginal() {\n" +
                "   //@ assert  6 == original_gcd(12, 18);\n" +
                "   //@ assert 15 == original_gcd(42, 56);\n" +
                "   }\n" +
                "   //@ requires a >= 0 & b >= 0 & (b > 0 | a > 0);\n" +
                "   //@ ensures  \\result > 0 & isGcd(\\result, a, b);\n" +
                "   //@ pure\n" +
                "   public static int iterative_gcd(int a, int b) {\n" +
                "	    /*@ maintaining a >= 0 & b >= 0;" +
                "         @ maintaining (\\forall int k;\n" +
                "	      @                       0 < k & k <= a;\n" +
                "         @                       isGcd(k, a, b) == isGcd(k, \\old(a), \\old(b)));\n" +
                "	      @ decreases   a + b;\n" +
                "         @*/\n" +
                "	    while (b != 0) {\n" +
                "	        int t = b;\n" +
                "	        b = a % b;\n" +
                "	        a = t;\n" +
                "	    }\n" +
                "	    return a;\n" +
                "    }\n" +
                "   public static void testIterative() {\n" +
                "   //@ assert  6 == original_gcd(12, 18);\n" +
                "   //@ assert 15 == original_gcd(42, 56);\n" +
                "   }\n" +
                "   //@ requires a >= 0 & b >= 0 & (b > 0 | a > 0);\n" +
                "   //@ ensures  \\result > 0 & isGcd(\\result, a, b);\n" +
                "   //@ pure\n" +
                "   public static int recursive_gcd(int a, int b) {\n" +
                "		if (b == 0)\n"+
                "          return a;\n" +
                "		else {\n"+
                "          //@ assert a % b < b;\n" +
                "          return recursive_gcd(b, a % b);\n" +
                "       }\n" +
                "    }\n" +
                "   public static void testRecursive() {\n" +
                "   //@ assert  6 == recursive_gcd(12, 18);\n" +
                "   //@ assert 15 == recursive_gcd(42, 56);\n" +
                "   }\n" +
                "}\n"
                },
                "----------\n" +
        		"1. ERROR in tests\\esc\\casestudy\\Euclid100.java (at line 57)\n" + 
        		"	//@ assert 15 == original_gcd(42, 56);\n" + 
        		"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
        		"Possible assertion failure (Assert).\n" + 
        		"----------\n"+
        		"2. ERROR in tests\\esc\\casestudy\\Euclid100.java (at line 77)\n" + 
        		"	//@ assert 15 == original_gcd(42, 56);\n" + 
        		"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
        		"Possible assertion failure (Assert).\n" + 
        		"----------\n"+
        		"3. ERROR in tests\\esc\\casestudy\\Euclid100.java (at line 92)\n" + 
        		"	//@ assert 15 == original_gcd(42, 56);\n" + 
        		"	           ^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
        		"Possible assertion failure (Assert).\n" + 
        		"----------\n");
    }
}
