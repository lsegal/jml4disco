package org.jmlspecs.eclipse.jdt.core.tests.dbc;
import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class OldTest extends AbstractRegressionTest {

	public final String workspace = "..";
	public final String path2jml4runtime = workspace + "/org.jmlspecs.jml4.runtime/bin";

    public OldTest(String name) {
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
        
    public void test_Neg_BoundedOccurOfQuaVarTest() {
      runNegativeTest(
          new String[] {
            "Neg_BoundedOccurOfQuaVarTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.old;\n" +
            "\n" +
            "public class Neg_BoundedOccurOfQuaVarTest {\n" +
            "   //@ ensures (\\forall int i; 0 <= i && i < 7; i < \\old(x));\n" +
            "   void foo(int x) {\n" +
            "      \n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

//    public void test_Neg_FreeOccurOfQuaVarTest() {
//      runNegativeTest(
//          new String[] {
//            "Neg_FreeOccurOfQuaVarTest.java",
//            "package org.jmlspecs.eclipse.jdt.core.tests.old;\n" +
//            "\n" +
//            "public class Neg_FreeOccurOfQuaVarTest {\n" +
//            "   //@ ensures (\\forall int i; 0 <= i && i < 7; \\old(i < x));\n" +
//            "   void foo(int x) {\n" +
//            "      \n" +
//            "   }\n" +
//            "}\n"
//          },
//          "----------\n" +
//          "1. ERROR in Neg_FreeOccurOfQuaVarTest.java\n" +
//          "----------\n");
//    }

    public void test_Neg_IncompatOldTest() {
      runNegativeTest(
          new String[] {
            "Neg_IncompatOldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.old;\n" +
            "\n" +
            "public class Neg_IncompatOldTest {\n" +
            "\n" +
            "   //@ ensures \\old(x) < \\result;\n" +
            "   String foo(int x) {\n" +
            "      return null;\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_IncompatOldTest.java (at line 5)\n" +
          "	//@ ensures \\old(x) < \\result;\n" + 
          "	            ^^^^^^^^^^^^^^^^^\n" + 
          "The operator < is undefined for the argument type(s) int, String\n" +
          "----------\n");
    }

    public void test_Neg_LabeldOldTest() {
      runNegativeTest(
          new String[] {
            "Neg_LabeldOldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.old;\n" +
            "\n" +
            "public class Neg_LabeldOldTest {\n" +
            "   void foo() {\n" +
            "      int i ;\n" +
            "      init: {\n" +
            "         i=0;\n" +
            "         i++;\n" +
            "         //@ assert i > \\old(i,init);\n" +
            "      }\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

//    public void test_Neg_LabeldOldTest2() {
//      runNegativeTest(
//          new String[] {
//            "Neg_LabeldOldTest2.java",
//            "package org.jmlspecs.eclipse.jdt.core.tests.old;\n" +
//            "\n" +
//            "public class Neg_LabeldOldTest2 {\n" +
//            "   void foo() {\n" +
//            "      int i ;\n" +
//            "      init: i=0;\n" +
//            "      i++;\n" +
//            "      //@ assert i > \\old(i,init);\n" +
//            "   }\n" +
//            "}\n"
//          },
//          "");
//    }

    public void test_Neg_NonprimOldTest() {
      runNegativeTest(
          new String[] {
            "Neg_NonprimOldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.old;\n" +
            "\n" +
            "public class Neg_NonprimOldTest {\n" +
            "   class Node {}\n" +
            "   \n" +
            "   //@ ensures \\old(x) == \\result;\n" +
            "   Node foo(Node x) {\n" +
            "      Node old = x;\n" +
            "      return old;\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_NonprimOldTest2() {
      runNegativeTest(
          new String[] {
            "Neg_NonprimOldTest2.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.old;\n" +
            "\n" +
            "public class Neg_NonprimOldTest2 {\n" +
            "   class Node {}\n" +
            "   \n" +
            "   //@ ensures \\old(x) > \\result;\n" +
            "   Node foo(Node x) {\n" +
            "      Node old = x;\n" +
            "      return old;\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_NonprimOldTest2.java (at line 6)\n" +
  		  "	//@ ensures \\old(x) > \\result;\n" + 
		  "	            ^^^^^^^^^^^^^^^^^\n" + 
          "The operator > is undefined for the argument type(s) org.jmlspecs.eclipse.jdt.core.tests.old.Neg_NonprimOldTest2.Node, org.jmlspecs.eclipse.jdt.core.tests.old.Neg_NonprimOldTest2.Node\n" +
          "----------\n");
    }

    public void test_Neg_OldTest() {
      runNegativeTest(
          new String[] {
            "Neg_OldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.old;\n" +
            "\n" +
            "public class Neg_OldTest {\n" +
            "\n" +
            "   //@ ensures \\old(x) < \\result;\n" +
            "   int foo(int x) {\n" +
            "      return x++;\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }
}

