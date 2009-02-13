package org.jmlspecs.eclipse.jdt.core.tests.dbc;
import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class ConstraintsTest extends AbstractRegressionTest {

	public final String workspace = "..";
	public final String path2jml4annotations = workspace + "/org.jmlspecs.annotation/bin";

    public ConstraintsTest(String name) {
        super(name);
    }
    
	protected String[] getDefaultClassPaths() {
		final String [] superDefaultClassPaths = super.getDefaultClassPaths();
		final int length = superDefaultClassPaths.length;
	    String[] defaultClassPaths = new String[length + 1];
        System.arraycopy(superDefaultClassPaths, 0, defaultClassPaths, 0, length);
        defaultClassPaths[length] = path2jml4annotations;
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
    
    public void test_001_ConstraintParsingTest() {
      runNegativeTest(
          new String[] {
            "Neg_ConstraintParsingTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.constraints;\n" +
            "public class Neg_ConstraintParsingTest {\n" +
            "   int count = -1;\n" +
            "   \n" +
            "   //@ constraint count > \\old(count);\n" +
            "   \n" +
            "   public void m(int num) {\n" +
            "        this.count = num;\n" +
            "    }\n" +
            "   \n" +
            "   public static void main(String args[]) {\n" +
            "      Neg_ConstraintParsingTest test = new Neg_ConstraintParsingTest();\n" +
            "      test.m(1);\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_002_InstConTest() {
      runNegativeTest(
          new String[] {
            "Neg_InstConTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.constraints;\n" +
            "public class Neg_InstConTest {\n" +
            "   int count = -1;\n" +
            "   \n" +
            "   //@ instance constraint count > \\old(count);\n" +
            "   \n" +
            "   public void m(int num) {\n" +
            "        this.count = num;\n" +
            "    }\n" +
            "   \n" +
            "   public static void main(String args[]) {\n" +
            "      Neg_InstConTest test = new Neg_InstConTest();\n" +
            "      test.m(1);\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_003_InstStaticConTest() {
      runNegativeTest(
          new String[] {
            "Neg_InstStaticConTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.constraints;\n" +
            "public class Neg_InstStaticConTest {\n" +
            "   static int count = -1;\n" +
            "   \n" +
            "   //@ instance static constraint count > \\old(count);\n" +
            "   \n" +
            "   public void m(int num) {\n" +
            "        count = num;\n" +
            "    }\n" +
            "   \n" +
            "   public static void main(String args[]) {\n" +
            "      Neg_InstStaticConTest test = new Neg_InstStaticConTest();\n" +
            "      test.m(1);\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_InstStaticConTest.java (at line 5)\n" +
          "\t//@ instance static constraint count > \\old(count);\n" +
          "\t    ^^^^^^^^^^^^^^^\n" +
          "Illegal modifier for the member declaration constraint; only either static or instance and other modifiers are permitted\n" +
          "----------\n");
    }

    public void test_004_InterfaceConstraintParsingTest() {
      runNegativeTest(
          new String[] {
            "Neg_InterfaceConstraintParsingTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.constraints;\n" +
            "public interface Neg_InterfaceConstraintParsingTest {\n" +
            "   int count = -1;\n" +
            "   \n" +
            "   //@ constraint count > \\old(count);   \n" +
            "}\n"
          },
          "");
    }

    public void test_005_InvariantParsingTest() {
      runNegativeTest(
          new String[] {
            "Neg_InvariantParsingTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.constraints;\n" +
            "public class Neg_InvariantParsingTest {\n" +
            "   int count = 1;\n" +
            "   \n" +
            "   //@ invariant count > 0;\n" +
            "   \n" +
            "   public void m(int num) {\n" +
            "        this.count = num;\n" +
            "    }\n" +
            "   \n" +
            "   public static void main(String args[]) {\n" +
            "      Neg_InvariantParsingTest test = new Neg_InvariantParsingTest();\n" +
            "      test.m(2);\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_006_StaticConTest() {
      runNegativeTest(
          new String[] {
            "Neg_StaticConTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.constraints;\n" +
            "public class Neg_StaticConTest {\n" +
            "   static int count = -1;\n" +
            "   \n" +
            "   //@ static constraint count > \\old(count);\n" +
            "   \n" +
            "   public void m(int num) {\n" +
            "        count = num;\n" +
            "    }\n" +
            "   \n" +
            "   public static void main(String args[]) {\n" +
            "      Neg_StaticConTest test = new Neg_StaticConTest();\n" +
            "      test.m(1);\n" +
            "   }\n" +
            "}\n"
          },
          "");
    }

    public void test_007_StaticInstConTest() {
      runNegativeTest(
          new String[] {
            "Neg_StaticInstConTest.java",
            "package org.jmlspecs.eclipse.jdt.core.tests.constraints;\n" +
            "public class Neg_StaticInstConTest {\n" +
            "   static int count = -1;\n" +
            "   \n" +
            "   //@ static instance constraint count > \\old(count);\n" +
            "   \n" +
            "   public void m(int num) {\n" +
            "        count = num;\n" +
            "    }\n" +
            "   \n" +
            "   public static void main(String args[]) {\n" +
            "      Neg_StaticInstConTest test = new Neg_StaticInstConTest();\n" +
            "      test.m(1);\n" +
            "   }\n" +
            "}\n"
          },
          "----------\n" +
          "1. ERROR in Neg_StaticInstConTest.java (at line 5)\n" +
          "\t//@ static instance constraint count > \\old(count);\n" +
          "\t    ^^^^^^^^^^^^^^^\n" +
          "Illegal modifier for the member declaration constraint; only either static or instance and other modifiers are permitted\n" +
          "----------\n");
    }
}