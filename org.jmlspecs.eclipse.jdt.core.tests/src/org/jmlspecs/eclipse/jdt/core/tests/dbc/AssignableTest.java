package org.jmlspecs.eclipse.jdt.core.tests.dbc;
import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class AssignableTest extends AbstractRegressionTest {

	public final String workspace = "..";
	public final String path2jml4runtime = workspace + "/org.jmlspecs.jml4.runtime/bin";

    public AssignableTest(String name) {
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
        
    public void test_Neg_ArraryRangeExpTest() {
      runNegativeTest(
          new String[] {
            "Neg_ArraryRangeExpTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_ArraryRangeExpTest {\n" +
            "   class A {\n" +
            "      A n[] = new A[5];\n" +
            "   }\n" +
            "   A a[] = new A[10];\n" +
            "   //@ assignable a[0..2], a[3..4].n, a[5..6].*;\n" +
            "   //@ assignable a[0].n[2..3], a[0].n[2..3].n;\n" +
            "   //@ assignable a[*], a[0].n[1].n[*], a[*].n, a[0].n[1].n[*].n;\n" +
            "   void m() {}\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_ArrayRefExpTest() {
      runNegativeTest(
          new String[] {
            "Neg_ArrayRefExpTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_ArrayRefExpTest {\n" +
            "   class A {      \n" +
            "      A[] l = new A[5];\n" +
            "      A n = new A();\n" +
            "   }\n" +
            "   \n" +
            "   A a = new A();\n" +
            "   A[] as = new A[4];\n" +
            "   int i[] = new int[10];\n" +
            "   int idx = 3;\n" +
            "   \n" +
            "   // assignable i[9], a.l[1], a.n.l[2], a.l[1].n, a.l[1].*;\n" +
            "   // assignable this.i[8], this.as[2].n, a.l[1].n.*;\n" +
            "   // assignable this.i[0..2], this.as[1..2].n;\n" +
            "   // assignable i[idx];\n" +
            "   //@ assignable a.l[1];\n" +
            "   void m() {}\n" +
            "}\n" +
            "\n"
          },
          "");
    }

    public void test_Neg_ErrorReportTest() {
      runNegativeTest(
          new String[] {
            "Neg_ErrorReportTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_ErrorReportTest {\n" +
            "   class A {\n" +
            "      int i;\n" +
            "      A next = new A();\n" +
            "   }\n" +
            "   \n" +
            "   class B extends A {\n" +
            "      int j;\n" +
            "   }\n" +
            "      \n" +
            "   A a = new A();\n" +
            "   A[] as = new A[10];\n" +
            "   \n" +
            "   //@ assignable a.*.next.next;\n" +
            "   //@ assignable this, Neg_ErrorReportTest.this;\n" +
            "   //@ assignable this.*.next.next;\n" +
            "   //@ assignable this.this.a, super.this;\n" +
            "   //@ assignable super;\n" +
            "   void m() {}\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_ErrorReportTest.java (at line 16)\n" +
          "\t//@ assignable a.*.next.next;\n" +
          "\t                 ^\n" +
          "Wildcard is not allowed at this location\n" +
          "----------\n" +
          "2. ERROR in Neg_ErrorReportTest.java (at line 17)\n" +
          "\t//@ assignable this, Neg_ErrorReportTest.this;\n" +
          "\t               ^^^^\n" +
          "The 'this' reference cannot be modified.\n" +
          "----------\n" +
          "3. ERROR in Neg_ErrorReportTest.java (at line 17)\n" +
          "\t//@ assignable this, Neg_ErrorReportTest.this;\n" +
          "\t                                         ^^^^\n" +
          "The 'this' reference cannot be modified.\n" +
          "----------\n" +
          "4. ERROR in Neg_ErrorReportTest.java (at line 18)\n" +
          "\t//@ assignable this.*.next.next;\n" +
          "\t                    ^\n" +
          "Wildcard is not allowed at this location\n" +
          "----------\n" +
          "5. ERROR in Neg_ErrorReportTest.java (at line 19)\n" +
          "\t//@ assignable this.this.a, super.this;\n" +
          "\t                    ^^^^\n" +
          "Keyword 'this' is not allowed at this location\n" +
          "----------\n" +
          "6. ERROR in Neg_ErrorReportTest.java (at line 19)\n" +
          "\t//@ assignable this.this.a, super.this;\n" +
          "\t                                  ^^^^\n" +
          "Keyword 'this' is not allowed at this location\n" +
          "----------\n" +
          "7. ERROR in Neg_ErrorReportTest.java (at line 20)\n" +
          "\t//@ assignable super;\n" +
          "\t               ^^^^^\n" +
          "The 'super' reference cannot be modified.\n" +
          "----------\n");
    }

    public void test_Neg_InformalDescTest() {
      runNegativeTest(
          new String[] {
            "Neg_InformalDescTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_InformalDescTest {\n" +
            "   //@ assignable (* informal desc *); \n" +
            "   void m() {}\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_QualifiedStoreRefTest() {
      runNegativeTest(
          new String[] {
            "Neg_QualifiedStoreRefTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_QualifiedStoreRefTest {\n" +
            "   int i;   \n" +
            "   Neg_QualifiedStoreRefTest x = new Neg_QualifiedStoreRefTest();   \n" +
            "   Neg_QualifiedStoreRefTest y = new Neg_QualifiedStoreRefTest();   \n" +
            "   Neg_QualifiedStoreRefTest z = new Neg_QualifiedStoreRefTest();   \n" +
            "   \n" +
            "   //@ assignable x.y.z.i, x.i, x.y;\n" +
            "   void m() {}\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_SimpleStoreRefsTest() {
      runNegativeTest(
          new String[] {
            "Neg_SimpleStoreRefsTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_SimpleStoreRefsTest {   \n" +
            "   int x;\n" +
            "   Neg_SimpleStoreRefsTest y = new Neg_SimpleStoreRefsTest();\n" +
            "   \n" +
            "   //@ assignable x, y;\n" +
            "   void m() {}\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_StaticFieldTest() {
      runNegativeTest(
          new String[] {
            "Neg_StaticFieldTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_StaticFieldTest {\n" +
            "   static int i;\n" +
            "   static Neg_StaticFieldTest x = new Neg_StaticFieldTest();\n" +
            "   \n" +
            "   //@ assignable Neg_StaticFieldTest.i, Neg_StaticFieldTest.x;\n" +
            "   void m() {}\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_StoreRefKeywordsTest() {
      runNegativeTest(
          new String[] {
            "Neg_StoreRefKeywordsTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_StoreRefKeywordsTest {\n" +
            "   //@ assignable \\nothing;\n" +
            "   void m1() {}\n" +
            "   \n" +
            "   //@ assignable \\everything;\n" +
            "   void m2() {}\n" +
            "   \n" +
            "   //@ assignable \\not_specified;\n" +
            "   void m3() {}\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_SuperInNameTest() {
      runNegativeTest(
          new String[] {
            "Neg_SuperInNameTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_SuperInNameTest {   \n" +
            "   class A {\n" +
            "      A a = new A();\n" +
            "      int i;\n" +
            "   }\n" +
            "   \n" +
            "   class B extends A {\n" +
            "      long l;\n" +
            "      //@ assignable super.a.i, super.a, super.*;\n" +
            "      void m() {}\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_SyntaxErrorReportTest() {
      runNegativeTest(
          new String[] {
            "Neg_SyntaxErrorReportTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_SyntaxErrorReportTest {\n" +
            "   class A {\n" +
            "      int i;\n" +
            "      A next = new A();\n" +
            "   }\n" +
            "   \n" +
            "   class B extends A {\n" +
            "      int j;\n" +
            "   }\n" +
            "      \n" +
            "   A a = new A();\n" +
            "   A[] as = new A[10];\n" +
            "   \n" +
            "   //@ assignable a.super, this.super;\n" +
            "   void m() {/*this.this.clone();*/}\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_SyntaxErrorReportTest.java (at line 16)\n" +
          "\t//@ assignable a.super, this.super;\n" +
          "\t                ^\n" +
          "Syntax error on token \".\", , expected\n" +
          "----------\n" +
          "2. ERROR in Neg_SyntaxErrorReportTest.java (at line 16)\n" +
          "\t//@ assignable a.super, this.super;\n" +
          "\t                            ^\n" +
          "Syntax error on token \".\", , expected\n" +
          "----------\n");
    }

    public void test_Neg_ThisInNameTest() {
      runNegativeTest(
          new String[] {
            "Neg_ThisInNameTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_ThisInNameTest {\n" +
            "   class A {\n" +
            "      int i;\n" +
            "   }\n" +
            "   \n" +
            "   class B extends A {\n" +
            "      A a = new A();\n" +
            "      long j;\n" +
            "      //@ assignable this.j, this.a.i, this.*;\n" +
            "      void m() {}\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_ThisSuffixTest() {
      runNegativeTest(
          new String[] {
            "Neg_ThisSuffixTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_ThisSuffixTest {\n" +
            "   \n" +
            "   class A {\n" +
            "      int i;\n" +
            "      \n" +
            "      class B {\n" +
            "         //@ assignable A.this.i, Neg_ThisSuffixTest.A.this.i;\n" +
            "         void m() {\n" +
            "            A.this.i = 1;\n" +
            "            Neg_ThisSuffixTest.A.this.i = 2;\n" +
            "         }               \n" +
            "      }\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_UnresolvableClauseTest() {
      runNegativeTest(
          new String[] {
            "Neg_UnresolvableClauseTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_UnresolvableClauseTest {\n" +
            "   //@ assignable notexist;\n" +
            "   void m() { /*y = 1;*/ }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_UnresolvableClauseTest.java (at line 4)\n" +
          "\t//@ assignable notexist;\n" +
          "\t               ^^^^^^^^\n" +
          "notexist cannot be resolved\n" +
          "----------\n");
    }

    public void test_Neg_WildcardTest() {
      runNegativeTest(
          new String[] {
            "Neg_WildcardTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.assignable;\n" +
            "\n" +
            "public class Neg_WildcardTest {   \n" +
            "   class A {\n" +
            "      int i;\n" +
            "   }\n" +
            "\n" +
            "   class B extends A {\n" +
            "      int j;\n" +
            "   }\n" +
            "\n" +
            "   B x = new B();\n" +
            "   \n" +
            "   //@ assignable x.*;\n" +
            "   void m() {}\n" +
            "}\n"
          },
          "");
    }
}