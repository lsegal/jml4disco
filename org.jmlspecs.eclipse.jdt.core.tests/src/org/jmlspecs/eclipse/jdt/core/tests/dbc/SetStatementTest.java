package org.jmlspecs.eclipse.jdt.core.tests.dbc;
import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class SetStatementTest extends AbstractRegressionTest {

	public final String workspace = "..";
	public final String path2jml4runtime = workspace + "/org.jmlspecs.jml4.runtime/bin";

    public SetStatementTest(String name) {
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

        return options;
    }
    
    public void test_Neg_GhostModTest() {
      runNegativeTest(
          new String[] {
            "Neg_GhostModTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_GhostModTest {\n" +
            "   //@ ghost int g = 0;\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_GhostSyntaxErrorTest() {
      runNegativeTest(
          new String[] {
            "Neg_GhostSyntaxErrorTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_GhostSyntaxErrorTest {\n" +
            "   //@ gghost int g = 0;\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_GhostSyntaxErrorTest.java (at line 4)\n" +
          "\t//@ gghost int g = 0;\n" +
          "\t    ^^^^^^\n" +
          "Syntax error on token \"gghost\", ghost expected\n" +
          "----------\n");
    }

    public void test_Neg_SetStmtOnArrayGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnArrayGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnArrayGhostFieldTest {\n" +
            "   //@ ghost int[] g = new int[3];\n" +
            "   void foo() {\n" +
            "      //@ set g[0] = 1;\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_SetStmtOnGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnGhostFieldTest {\n" +
            "   //@ ghost int g = 0;\n" +
            "   void foo() {\n" +
            "      //@ set g = 1;\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_SetStmtOnGhostLocalTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnGhostLocalTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnGhostLocalTest {\n" +
            "   void foo() {\n" +
            "      //@ ghost int g = 0;\n" +
            "      //@ set g = 1;\n" +
            "      //@ assert g == 1;\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_SetStmtOnMthdCallTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnMthdCallTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnMthdCallTest {\n" +
            "   void foo() {\n" +
            "      //@ set bar();\n" +
            "   }\n" +
            "   \n" +
            "   void bar() { }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SetStmtOnMthdCallTest.java (at line 5)\n" +
          "\t//@ set bar();\n" +
          "\t            ^\n" +
          "Syntax error, insert \"AssignmentOperator Expression\" to complete Assignment\n" +
          "----------\n");
    }

    public void test_Neg_SetStmtOnQualGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnQualGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnQualGhostFieldTest {\n" +
            "   void foo() {\n" +
            "      Mid m = new Mid();\n" +
            "      //@ set m.b.h = 1;\n" +
            "   }\n" +
            "   \n" +
            "   class Mid {\n" +
            "      Bar b = new Bar();\n" +
            "   }\n" +
            "\n" +
            "   class Bar {   \n" +
            "      //@ ghost int h;\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_SetStmtOnSuperGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnSuperGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnSuperGhostFieldTest extends BarOfSuperGhostFieldTest {\n" +
            "   void foo() {      \n" +
            "      BarOfSuperGhostFieldTest b = new BarOfSuperGhostFieldTest();\n" +
            "      //@ set super.h = 1;\n" +
            "      //@ set b.h = 2;\n" +
            "   }\n" +
            "}\n" +
            "\n" +
            "class BarOfSuperGhostFieldTest {   \n" +
            "   //@ protected ghost int h;\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_SetStmtOnThisGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnThisGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnThisGhostFieldTest {\n" +
            "   //@ ghost int g;\n" +
            "   void foo() {\n" +
            "      //@ set this.g = 1;\n" +
            "   }\n" +
            "}\n" +
            "\n"
          },
          "");
    }

    public void test_Neg_SetStmtOnUndefArrayGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnUndefArrayGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnUndefArrayGhostFieldTest {\n" +
            "   int[] g = new int[3];\n" +
            "   void foo() {\n" +
            "      //@ set g[0] = 1;\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SetStmtOnUndefArrayGhostFieldTest.java (at line 6)\n" +
          "\t//@ set g[0] = 1;\n" +
          "\t        ^\n" +
          "g cannot be resolved\n" +
          "----------\n");
    }

    public void test_Neg_SetStmtOnUndefGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnUndefGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnUndefGhostFieldTest {\n" +
            "   int g = 0;\n" +
            "   \n" +
            "   void foo() {      \n" +
            "      //@ set g = 1;\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SetStmtOnUndefGhostFieldTest.java (at line 7)\n" +
          "\t//@ set g = 1;\n" +
          "\t        ^\n" +
          "g cannot be resolved\n" +
          "----------\n");
    }

    public void test_Neg_SetStmtOnUndefGhostLocalTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnUndefGhostLocalTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnUndefGhostLocalTest {\n" +
            "   void foo() {      \n" +
            "      int g = 0;\n" +
            "      //@ set g = 1;\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SetStmtOnUndefGhostLocalTest.java (at line 6)\n" +
          "\t//@ set g = 1;\n" +
          "\t        ^\n" +
          "g cannot be resolved\n" +
          "----------\n");
    }

    public void test_Neg_SetStmtOnUndefQualGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnUndefQualGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnUndefQualGhostFieldTest {\n" +
            "   void foo() {\n" +
            "      Mid m = new Mid();\n" +
            "      //@ set m.b.h = 1;\n" +
            "   }\n" +
            "   \n" +
            "   class Mid {\n" +
            "      Bar b = new Bar();\n" +
            "   }\n" +
            "\n" +
            "   class Bar {   \n" +
            "      int h;\n" +
            "   }\n" +
            "}\n" +
            "\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SetStmtOnUndefQualGhostFieldTest.java (at line 6)\n" +
          "\t//@ set m.b.h = 1;\n" +
          "\t        ^\n" +
          "h cannot be resolved\n" +
          "----------\n");
    }

    public void test_Neg_SetStmtOnUndefSuperGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnUndefSuperGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnUndefSuperGhostFieldTest extends BarOfUndefSuperGhostFieldTest {\n" +
            "   void foo() {      \n" +
            "      BarOfUndefSuperGhostFieldTest b = new BarOfUndefSuperGhostFieldTest();\n" +
            "      //@ set super.i = 1;\n" +
            "      //@ set b.h = 2;\n" +
            "   }\n" +
            "}\n" +
            "\n" +
            "class BarOfUndefSuperGhostFieldTest {\n" +
            "   protected int i;\n" +
            "   //@ protected ghost int h;\n" +
            "}\n" +
            "\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SetStmtOnUndefSuperGhostFieldTest.java (at line 6)\n" +
          "\t//@ set super.i = 1;\n" +
          "\t              ^\n" +
          "The field BarOfUndefSuperGhostFieldTest.i is not visible\n" +
          "----------\n");
    }

    public void test_Neg_SetStmtOnUndefThisGhostFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnUndefThisGhostFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnUndefThisGhostFieldTest {\n" +
            "   int g;\n" +
            "   void foo() {\n" +
            "      //@ set this.g = 1;\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SetStmtOnUndefThisGhostFieldTest.java (at line 6)\n" +
          "\t//@ set this.g = 1;\n" +
          "\t             ^\n" +
          "The field Neg_SetStmtOnUndefThisGhostFieldTest.g is not visible\n" +
          "----------\n");
    }

    public void test_Neg_SetStmtOnUnDefVarTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetStmtOnUnDefVarTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetStmtOnUnDefVarTest {\n" +
            "   void foo() {\n" +
            "      //@ set g = 1;\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SetStmtOnUnDefVarTest.java (at line 5)\n" +
          "\t//@ set g = 1;\n" +
          "\t        ^\n" +
          "g cannot be resolved\n" +
          "----------\n");
    }

    public void test_Neg_SetSyntaxErrorTest() {
      runNegativeTest(
          new String[] {
            "Neg_SetSyntaxErrorTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.setstmt;\n" +
            "\n" +
            "public class Neg_SetSyntaxErrorTest {\n" +
            "   void foo() {\n" +
            "      //@ sset g = 1;\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SetSyntaxErrorTest.java (at line 5)\n" +
          "\t//@ sset g = 1;\n" +
          "\t    ^^^^\n" +
          "sset cannot be resolved to a type\n" +
          "----------\n");
    }
}