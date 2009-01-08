package org.jmlspecs.eclipse.jdt.core.tests.dbc;
import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class TypeTest extends AbstractRegressionTest {

	public final String workspace = "..";
	public final String path2jml4runtime = workspace + "/org.jmlspecs.jml4.runtime/bin";

    public TypeTest(String name) {
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
        
    public void test_Neg_ArrayTypeofTest() {
      runNegativeTest(
          new String[] {
            "Neg_ArrayTypeofTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_ArrayTypeofTest {\n" +
            "   //@ requires \\typeof(c) == \\type(String[]);\n" +
            "   void foo(String[] c) {\n" +
            "      /* ... */\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_ArrayTypeVarTest() {
      runNegativeTest(
          new String[] {
            "Neg_ArrayTypeVarTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_ArrayTypeVarTest<T> {\n" +
            "   //@ requires \\typeof(c) == \\type(T[]);\n" +
            "   void foo(T[] c) {\n" +
            "      /* ... */\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_ArrayTypeVarTest.java (at line 4)\n" +
          "\t//@ requires \\typeof(c) == \\type(T[]);\n" +
          "\t             ^^^^^^^^^^\n" +
          "Illegal class literal for the type parameter T\n" +
          "----------\n" +
          "2. ERROR in Neg_ArrayTypeVarTest.java (at line 4)\n" +
          "\t//@ requires \\typeof(c) == \\type(T[]);\n" +
          "\t                           ^^^^^^^^^^\n" +
          "Illegal class literal for the type parameter T\n" +
          "----------\n");
    }

    public void test_Neg_BooleanTypeofTest() {
      runNegativeTest(
          new String[] {
            "Neg_BooleanTypeofTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_BooleanTypeofTest {\n" +
            "   //@ requires \\typeof(b) == \\type(boolean);\n" +
            "   void foo(boolean b) {\n" +
            "      /* ... */\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_BooleanTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_BooleanTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_BooleanTypeTest {\n" +
            "   //@ requires \\type(boolean) == Boolean.TYPE;\n" +
            "   void foo(boolean b) {\n" +
            "      /* ... */\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_Elem_ClassArgTest() {
      runNegativeTest(
          new String[] {
            "Neg_Elem_ClassArgTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_Elem_ClassArgTest {\n" +
            "   Class<Integer[]> c = Integer[].class;\n" +
            "   //@ invariant \\elemtype(c) == \\type(boolean);\n" +
            "   // Currently, the above invariant is considered to pass type resolution phase.\n" +
            "   // Perhaps it may be better to analyze variable c and extract \\type(int) in the future.\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_Elem_MulIntArrayTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_Elem_MulIntArrayTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_Elem_MulIntArrayTypeTest {\n" +
            "   //@ invariant \\elemtype(\\type(int[][])) == \\type(int[]);\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_Elem_NonArrayTest() {
      runNegativeTest(
          new String[] {
            "Neg_Elem_NonArrayTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_Elem_NonArrayTest {\n" +
            "   //@ invariant \\elemtype(\\type(int)) == null;\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_Elem_NonClassArgTest() {
      runNegativeTest(
          new String[] {
            "Neg_Elem_NonClassArgTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_Elem_NonClassArgTest {\n" +
            "   int i[];\n" +
            "   //@ invariant \\elemtype(i) == \\type(int);\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_Elem_NonClassArgTest.java (at line 5)\n" +
          "\t//@ invariant \\elemtype(i) == \\type(int);\n" +
          "\t              ^^^^^^^^^^^^\n" +
          "Type mismatch: cannot convert from int[] to Class<T>\n" +
          "----------\n");
    }

    public void test_Neg_Elem_ObjTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_Elem_ObjTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_Elem_ObjTypeTest {\n" +
            "   //@ invariant \\elemtype(\\type(Object)) == null;\n" +
            "   //@ invariant \\elemtype(\\type(Object)) == \\type(int);\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_Elem_TypeofTest() {
      runNegativeTest(
          new String[] {
            "Neg_Elem_TypeofTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_Elem_TypeofTest {\n" +
            "   int i[] = {1};\n" +
            "   //@ invariant \\elemtype(\\typeof(i)) == \\type(int);\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_Elem_VoidArrayTest() {
      runNegativeTest(
          new String[] {
            "Neg_Elem_VoidArrayTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_Elem_VoidArrayTest {\n" +
            "   //@ invariant \\elemtype(\\type(void[])) == \\type(int);\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_Elem_VoidArrayTest.java (at line 4)\n" +
          "\t//@ invariant \\elemtype(\\type(void[])) == \\type(int);\n" +
          "\t                              ^^^^^^\n" +
          "void[] is an invalid type\n" +
          "----------\n");
    }

    public void test_Neg_Elem_VoidArrayTest2() {
      runNegativeTest(
          new String[] {
            "Neg_Elem_VoidArrayTest2.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_Elem_VoidArrayTest2 {\n" +
            "   void[] vs;\n" +
            "   //@ invariant \\elemtype(\\typeof(vs)) == \\type(int);\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_Elem_VoidArrayTest2.java (at line 4)\n" +
          "\tvoid[] vs;\n" +
          "\t^^^^^^\n" +
          "void[] is an invalid type\n" +
          "----------\n" +
          "2. ERROR in Neg_Elem_VoidArrayTest2.java (at line 5)\n" +
          "\t//@ invariant \\elemtype(\\typeof(vs)) == \\type(int);\n" +
          "\t                                ^^\n" +
          "vs cannot be resolved\n" +
          "----------\n");
    }

    public void test_Neg_ElemtypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_ElemtypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_ElemtypeTest {\n" +
            "   //@ invariant \\elemtype(\\type(int[])) == \\type(int);\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_GenericClassTest() {
      runNegativeTest(
          new String[] {
            "Neg_GenericClassTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_GenericClassTest {\n" +
            "   class GenClass<T> {}\n" +
            "   \n" +
            "   GenClass<Object> gc = new GenClass<Object>();\n" +
            "   \n" +
            "   //@ invariant \\typeof(gc) == \\type(GenClass<Object>);\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_IncompatiableTypesTest() {
      runNegativeTest(
          new String[] {
            "Neg_IncompatiableTypesTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_IncompatiableTypesTest {\n" +
            "   String s = \"str\";\n" +
            "   Object o = new Object();\n" +
            "   //@ invariant \\type(String) == \\type(Object);\n" +
            "   //@ invariant \\typeof(s) == \\typeof(o);\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_IncompatiableTypesTest.java (at line 6)\n" +
          "\t//@ invariant \\type(String) == \\type(Object);\n" +
          "\t              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
          "Incompatible operand types Class<String> and Class<Object>\n" +
          "----------\n" +
          "2. ERROR in Neg_IncompatiableTypesTest.java (at line 7)\n" +
          "\t//@ invariant \\typeof(s) == \\typeof(o);\n" +
          "\t              ^^^^^^^^^^^^^^^^^^^^^^^^\n" +
          "Incompatible operand types Class<String> and Class<Object>\n" +
          "----------\n");
    }

    public void test_Neg_IntAndIntegerArrayTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_IntAndIntegerArrayTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_IntAndIntegerArrayTypeTest {\n" +
            "   //@ invariant \\type(int[]) == Integer[].class;\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_IntAndIntegerArrayTypeTest.java (at line 4)\n" +
          "\t//@ invariant \\type(int[]) == Integer[].class;\n" +
          "\t              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
          "Incompatible operand types Class<int[]> and Class<Integer[]>\n" +
          "----------\n");
    }

    public void test_Neg_IntArrayTypeofTest() {
      runNegativeTest(
          new String[] {
            "Neg_IntArrayTypeofTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_IntArrayTypeofTest {\n" +
            "   Integer integers[];\n" +
            "   int ints[];\n" +
            "   //@ invariant \\typeof(integers) == Integer[].class;\n" +
            "   //@ invariant \\typeof(ints) == Integer[].class;\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_IntArrayTypeofTest.java (at line 7)\n" +
          "\t//@ invariant \\typeof(ints) == Integer[].class;\n" +
          "\t              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
          "Incompatible operand types Class<int[]> and Class<Integer[]>\n" +
          "----------\n");
    }

    public void test_Neg_IntegerArrayTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_IntegerArrayTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_IntegerArrayTypeTest {\n" +
            "   //@ invariant \\type(Integer[]) == Integer[].class;\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_MulIntegerArrayTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_MulIntegerArrayTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_MulIntegerArrayTypeTest {\n" +
            "   //@ invariant \\type(Integer[][]) == Integer[][].class;\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_StringArrayTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_StringArrayTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_StringArrayTypeTest {\n" +
            "   //@ requires \\type(String[]) == String[].class;\n" +
            "   void foo(String[] c) {\n" +
            "      /* ... */\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_StringTypeofTest() {
      runNegativeTest(
          new String[] {
            "Neg_StringTypeofTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_StringTypeofTest {\n" +
            "   //@ requires \\typeof(c) == \\type(String);\n" +
            "   void foo(String c) {\n" +
            "      /* ... */\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_StringTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_StringTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_StringTypeTest {\n" +
            "   //@ requires \\type(String) == String.class;\n" +
            "   void foo(String c) {\n" +
            "      /* ... */\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_Neg_TypeVarTypeofTest() {
      runNegativeTest(
          new String[] {
            "Neg_TypeVarTypeofTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_TypeVarTypeofTest<T> {\n" +
            "   //@ requires \\typeof(c) == \\type(T);\n" +
            "   void foo(T c) {\n" +
            "      /* ... */\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_TypeVarTypeofTest.java (at line 4)\n" +
          "\t//@ requires \\typeof(c) == \\type(T);\n" +
          "\t             ^^^^^^^^^^\n" +
          "Illegal class literal for the type parameter T\n" +
          "----------\n" +
          "2. ERROR in Neg_TypeVarTypeofTest.java (at line 4)\n" +
          "\t//@ requires \\typeof(c) == \\type(T);\n" +
          "\t                           ^^^^^^^^\n" +
          "Illegal class literal for the type parameter T\n" +
          "----------\n");
    }

    public void test_Neg_TypeVarTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_TypeVarTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_TypeVarTypeTest<T> {\n" +
            "   //@ requires \\type(T) == T.class;\n" +
            "   void foo(T c) {      \n" +
            "      /* ... */\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_TypeVarTypeTest.java (at line 4)\n" +
          "\t//@ requires \\type(T) == T.class;\n" +
          "\t             ^^^^^^^^\n" +
          "Illegal class literal for the type parameter T\n" +
          "----------\n" +
          "2. ERROR in Neg_TypeVarTypeTest.java (at line 4)\n" +
          "\t//@ requires \\type(T) == T.class;\n" +
          "\t                         ^^^^^^^\n" +
          "Illegal class literal for the type parameter T\n" +
          "----------\n");
    }

    public void test_Neg_VoidArrayTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_VoidArrayTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_VoidArrayTypeTest {\n" +
            "   //@ invariant \\type(void[]) == Void[].class;\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_VoidArrayTypeTest.java (at line 4)\n" +
          "\t//@ invariant \\type(void[]) == Void[].class;\n" +
          "\t                    ^^^^^^\n" +
          "void[] is an invalid type\n" +
          "----------\n");
    }

    public void test_Neg_VoidTypeTest() {
      runNegativeTest(
          new String[] {
            "Neg_VoidTypeTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.type;\n" +
            "\n" +
            "public class Neg_VoidTypeTest {\n" +
            "   //@ invariant \\type(void) == Void.TYPE;\n" +
            "}\n"
          },
          "");
    }
}