package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class AnnotatedLoopTest extends AbstractRegressionTest {

	public AnnotatedLoopTest(String name) {
		super(name);
	}

	// Augment problem detection settings
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
	    Map<String, String> options = super.getCompilerOptions();

	    options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NON_NULL);
	    options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.ENABLED);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportNonStaticAccessToStatic, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_SpecPath, DbcTestCompiler.getSpecPath());
	    return options;
	}

    public void test_0001_while_true() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m(boolean b) { \n" +
                "   	//@ loop_invariant true;\n" +
                "   	while (b) {} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0002_while_expr() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m(int i, String s) { \n" +
                "   	//@ loop_invariant s.length() * 2 < i;\n" +
                "   	while (true) {} \n" +
                "	}\n" +
                "}\n"
                },"");
    }
    public void test_0003_while_int() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m(int i, String s) { \n" +
                "   	//@ loop_invariant i;\n" +
                "   	while (true) {} \n" +
                "	}\n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 3)\n" +
                "	//@ loop_invariant i;\n" +
                "	                   ^\n" +
                "Type mismatch: cannot convert from int to boolean\n" +
                "----------\n");
    }
    public void test_0004_while_RAC_valid() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   	//@ loop_invariant sum >= 0;\n" +
                "   	while (i < vals.length) { sum += vals[i++]; } \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0005_while_RAC_invalid() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "       try {\n" +
                "   	   int sum = 0;\n" +
                "   	   //@ loop_invariant sum == 111;\n" +
                "   	   while (i < vals.length) { sum += vals[i++]; } \n" +
                "	    } catch (Error e) {\n" +
                "          System.out.println(e.toString());\n" +
                "	    }\n" +
                "	}\n" +
                "}\n"
                },
        		"java.lang.Error: loop_invariant clause failed ('(sum == 111)')");
    }
    public void test_0006_while_RAC_constTrue() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "       try {\n" +
                "   	   int sum = 0;\n" +
                "   	   //@ loop_invariant sum == 111;\n" +
                "   	   while (true) { sum += vals[i++]; } \n" +
                "	    } catch (Error e) {\n" +
                "          System.out.println(e.toString());\n" +
                "	    }\n" +
                "	}\n" +
                "}\n"
                },
        		"java.lang.Error: loop_invariant clause failed ('(sum == 111)')");
    }
    public void test_0007_while_RAC_constFalse() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   static final boolean DBG = false;" +
                "   public static void main(String[] args) { \n" +
                "       new X().m(new X());\n" +
                "   }\n" +
                "   void m(X x) {\n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "       try {\n" +
                "   	   int sum = 0;\n" +
                "   	   //@ loop_invariant sum == 111;\n" +
                "   	   while (x.DBG) { /*empty*/ } \n" +
                "	    } catch (Error e) {\n" +
                "          System.out.println(e.toString());\n" +
                "	    }\n" +
                "	}\n" +
                "}\n"
                },
        		"java.lang.Error: loop_invariant clause failed ('(sum == 111)')");
    }
    public void test_0008_while_RAC_noBody() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "       try {\n" +
                "   	   int sum = 0;\n" +
                "   	   //@ loop_invariant sum == 111;\n" +
                "   	   while (i == i) { /* empty */ } \n" +
                "	    } catch (Error e) {\n" +
                "          System.out.println(e.toString());\n" +
                "	    }\n" +
                "	}\n" +
                "}\n"},
        		"java.lang.Error: loop_invariant clause failed ('(sum == 111)')");
    }

    public void test_0009_while_RAC_throwBody() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "      new X().m();\n" +
                "   }\n" +
                "   boolean bool() { return true; }\n" +
                "   void m() {" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "       try {\n" +
                "   	   int sum = 0;\n" +
                "   	   //@ loop_invariant sum == 111;\n" +
                "   	   while (bool()) { throw new RuntimeException(); } \n" +
                "	    } catch (Error e) {\n" +
                "          System.out.println(e.toString());\n" +
                "	    }\n" +
                "	}\n" +
                "}\n"},
        		"java.lang.Error: loop_invariant clause failed ('(sum == 111)')");
    }
    public void test_0010_while_RAC_break_valid() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   	//@ loop_invariant sum >= 0;\n" +
                "   	while (i < vals.length) { break; } \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void _test_0011_while_RAC_break_invalid() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "       try {\n" +
                "   	   int sum = 0;\n" +
                "   	   //@ loop_invariant sum >= 0;\n" +
                "   	   while (i < vals.length) { sum = -1; break; } \n" +
                "	    } catch (Error e) {\n" +
                "          System.out.println(e.toString());\n" +
                "	    }\n" +
                "	}\n" +
                "}\n"
                },
        		"java.lang.Error: loop_invariant clause failed ('(sum >= 0)')");
    }
    public void test_0012_while_true() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m(boolean b) { \n" +
                "   	//@ maintaining true;\n" +
                "   	while (b) {} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    // FIXME: [Chalin] There is no break in the following test so
    // I am assuming the test is wrong. It takes very long to run
    // the test so I am disabling it.
    public void _test_0013_while_RAC_break_valid() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int j = 100;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   	//@ loop_invariant sum >= 0;\n" +
                "   	while (i < vals.length) {\n" +
                "   	      //@ loop_invariant i%2 < 2;\n" +
                "   	      while (i % 2 > 2) { j--;}\n" +
                "   	      i--;\n" +
                "        }\n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0014_while_RAC_seq() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   	//@ loop_invariant sum >= 0;\n" +
                "   	//@ loop_invariant 0 <= 0;\n" +
                "   	//@ loop_invariant sum >= 0;\n" +
                "   	//@ loop_invariant 0 <= 0;\n" +
                "   	while (i < vals.length) { sum += vals[i++]; } \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0015_while_leq_expr_RAC() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   	//@ loop_invariant 0 <= sum;\n" +
                "   	while (i < vals.length) { sum += vals[i++]; } \n" +
                "	}\n" +
                "}\n"
                },"");
    }
    public void test_0101_while_variant_int() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n" +
                "   public void m(int i) { \n" +
                "   	//@ decreases i;\n" +
                "   	while (i > 0) {} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0102_while_variant_bool() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n" +
                "   public void m(boolean b) { \n" +
                "   	//@ decreases b;\n" +
                "   	while (b) {} \n" +
                "	}\n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 3)\n" +
                "	//@ decreases b;\n" +
                "	              ^\n" +
                "Type mismatch: cannot convert from boolean to int\n" +
                "----------\n");
    }
    public void test_0110_while_RAC_valid_variant() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   	//@ decreases vals.length - i;\n" +
                "   	while (i < vals.length) { sum += vals[i++]; } \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0111_while_RAC_invalid_variant() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "     try {\n" +
                "   	int i = 3;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   	//@ decreases i;\n" +
                "   	while (i < vals.length) { sum += vals[i++]; } \n" +
                "     } catch (Error e) {\n" +
                "        System.out.println(e.toString());\n" +
                "     }\n" +
                "	}\n" +
                "}\n"
                },
                "java.lang.Error: loop variant did not decrease ('i')");
    }
    public void test_0112_while_RAC_invalid_variant() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void f(int[] vals) { \n" +
                "   	int i = 20;\n" +
                "   	int sum = 0;\n" +
                "   	//@ decreases i;\n" +
                "   	while (i <= 20) { i--; } \n" +
                "   }\n" +
                "   public static void main(String[] args) { \n" +
                "     try {\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "       f(vals);\n" +
                "     } catch (Error e) {\n" +
                "        System.out.println(e.toString());\n" +
                "     }\n" +
                "	}\n" +
                "}\n"
                },
        		"java.lang.Error: loop variant negative ('i')");
    }
    public void test_0113_while_RAC_valid_variant() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   try {\n" +
                "       //@ decreases vals.length - i;\n" +
                "       while (i < vals.length) {\n" +
                "             //@ decreases vals.length - i;\n" +
                "             while (i%2==0) \n" +
                "                   sum += vals[i--]; } \n" +
                "   } catch (Error e) {System.out.println(e);}\n" +
                "	}\n" +
                "}\n"
                },
		"java.lang.Error: loop variant did not decrease ('(vals.length - i)')");
    }
    public void test_0114_while_RAC_invalid_variant() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   try {\n" +
                "       //@ decreases vals.length - i;\n" +
                "       while (i < vals.length) {\n" +
                "             //@ decreases i;\n" +
                "             while (i%2==0) \n" +
                "                   sum += vals[i++]; } \n" +
                "   } catch (Error e) {System.out.println(e);}\n" +
                "	}\n" +
                "}\n"
                },
                "java.lang.Error: loop variant did not decrease ('i')");
    }
    public void test_0115_while_RAC_invalid_variant() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   try {\n" +
                "       //@ decreases  i;\n" +
                "       while (i < vals.length) {\n" +
                "             //@ decreases vals.length - i;\n" +
                "             while (i%2==0) \n" +
                "                   sum += vals[i++]; } \n" +
                "   } catch (Error e) {System.out.println(e);}\n" +
                "	}\n" +
                "}\n"
                },
		"java.lang.Error: loop variant did not decrease ('i')");
    }
    public void test_0116_while_RAC_seq() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   	//@ decreases (vals.length - i+10);\n" +
                "   	//@ decreases (vals.length - i+5);\n" +
                "   	//@ decreases (vals.length - i+1);\n" +
                "   	while (i < vals.length) { sum += vals[i++]; } \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0117_while_RAC_seq() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "   	int[] vals = new int[] {2,3,5,7,9};\n" +
                "   	int sum = 0;\n" +
                "   	//@ loop_invariant sum >= 0;\n" +
                "   	//@ loop_invariant i >= 0;\n" +
                "   	//@ loop_invariant  vals.length >= i;\n" +
                "   	while (i < vals.length) { sum += vals[i++]; } \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0200_while_synonyms() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m() { \n" +
                "   	//@ loop_invariant true;\n" +
                "   	while (true) {/**/} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0201_while_synonyms() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m() { \n" +
                "   	//@ loop_invariant_redundantly true;\n" +
                "   	while (true) {/**/} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0202_while_synonyms() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m() { \n" +
                "   	//@ maintaining true;\n" +
                "   	while (true) {/**/} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0203_while_synonyms() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m() { \n" +
                "   	//@ maintaining_redundantly true;\n" +
                "   	while (true) {/**/} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0204_while_synonyms() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m() { \n" +
                "   	//@ decreases 0;\n" +
                "   	while (true) {/**/} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0205_while_synonyms() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m() { \n" +
                "   	//@ decreases 0;\n" +
                "   	while (true) {/**/} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0206_while_synonyms() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m() { \n" +
                "   	//@ decreasing_redundantly 0;\n" +
                "   	while (true) {/**/} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0207_while_synonyms() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m() { \n" +
                "   	//@ decreasing_redundantly 0;\n" +
                "   	while (true) {/**/} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0300_while_label() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m(boolean b) { \n" +
                "   	//@ loop_invariant true;\n" +
                "   	here: while (b) { break here;} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0401_for_invariant() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m(boolean b) { \n" +
                "   	//@ loop_invariant true;\n" +
                "   	for (int i=0; i<10; i++) {} \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0402_for_invalid() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m(boolean b) { \n" +
                "   	//@ loop_invariant 3;\n" +
                "   	for (int i=0; i<10; i++) {} \n" +
                "	}\n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 3)\n" +
                "	//@ loop_invariant 3;\n" +
                "	                   ^\n" +
                "Type mismatch: cannot convert from int to boolean\n" +
                "----------\n");
    }
    public void test_0401_do_invariant() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m(boolean b) { \n" +
                "   	//@ loop_invariant true;\n" +
                "   	do {} while (b); \n" +
                "	}\n" +
                "}\n"
                },
                "");
    }
    public void test_0402_do_invalid() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public void m(boolean b) { \n" +
                "   	//@ loop_invariant 3;\n" +
                "   	do {} while (b); \n" +
                "	}\n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 3)\n" +
                "	//@ loop_invariant 3;\n" +
                "	                   ^\n" +
                "Type mismatch: cannot convert from int to boolean\n" +
                "----------\n");
    }
	public void test_1000_while_sideEffectsInCondition() {
		this.runConformTest(new String[] {
				"X.java",
				"public class X {\n" +
                "   public static void main(String[] args) { \n" +
                "	   try {\n" +
                "	      noSideEffects(10);" +
                "      } catch (Throwable t) {\n" +
                "         System.out.println(\"1\" + t.toString());" +
                "	   }\n" +
                "	   try {\n" +
                "	      withSideEffects(10);" +
                "      } catch (Throwable t) {\n" +
                "         System.out.println(\"1\" + t.toString());" +
                "	   }\n" +
                "	   try {\n" +
                "	      withSideEffects_varAndInvar(10);" +
                "      } catch (Throwable t) {\n" +
                "         System.out.println(\"1\" + t.toString());" +
                "	   }\n" +
                "	   System.out.println(\"success\");\n" +
                "	}\n" +
				"	public static void noSideEffects(int b) {\n" +
				"		//@ assume b >= 0;\n" +
				"		int i = b;\n" +
				"		//@ maintaining i+1 >= 0;\n" +
				"		//@ decreasing i+1;\n" +
				"		while (i >= 0) {\n" +
				"		      i--;\n" +
				"		}\n" +
				"		//@ assert i == -1;\n" +
				"	}\n" + 
				"	public static void withSideEffects_varAndInvar(final int b) {\n" +
				"		//@ assume b >= 0;\n" +
				"		int i = b;\n" +
				"		//@ maintaining i+1 >= 0;\n" +
				"		//@ decreasing i+1;\n" +
				"		while (i-- >= 0) {\n" +
				"		}\n" +
				"		//@ assert i == -2;\n" +
				"	}\n" + 
				"	public static void withSideEffects(final int b) {\n" +
				"		//@ assume b >= 0;\n" +
				"		int i = b;\n" +
				"		//@ maintaining i+1 >= 0;\n" +
				"		while (i-- >= 0) {\n" +
				"		}\n" +
				"		//@ assert i == -2;\n" +
				"	}\n" + 
				"}\n"
				},
				"success");
	}

}
