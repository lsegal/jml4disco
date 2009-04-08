package org.jmlspecs.eclipse.jdt.core.tests.nonnull;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class NNTS_MonoTestRuntime extends AbstractRegressionTest {

	public NNTS_MonoTestRuntime(String name) { 
	    super(name);
	}

	// Augment problem detection settings
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
	    Map<String, String> options = super.getCompilerOptions();

	    options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NULLABLE);
	    options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.ENABLED);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_SpecPath, NullTypeSystemTestCompiler.getSpecPath());
	    return options;
	}


	public void test_0000_Mono_Sanity() {
		this.runConformTest(
			new String[] {
				"Mono_Sanity.java",
	            "import java.io.*;\n" +
	            "public class Mono_Sanity {\n" +
	            "   public static void main(String [] args) {\n"+
	            "       PrintStream out = System.out;\n" +
	            "       if (out != null)\n" +
	            "           out.println(\"SUCCESS!\");\n"+
	            "   }\n"+
	            "}\n"
			},
			"SUCCESS!");
	}

	public void test_0001_Mono_Assign() {
		this.runConformTest(
			new String[] {
				"Mono_Assign.java",
	            "public class Mono_Assign {\n" +
                "   /*@mono_non_null*/ String f1;\n" +
                "   /*@mono_non_null*/ String f2;\n" +
                "   /*@nullable*/      String n1;\n" +
                "   /*@mono_non_null*/ String f3;\n" +
                "   public static void main(String[] args) {\n" +
                "      new Mono_Assign().m();\n" +
                "   }\n" +
                "   void m() {\n" +
                "	   try {\n" +
                "         f1 = \"world\";\n" +
                "      } catch (Throwable t) {\n" +
                "         System.out.println(\"Failure\");\n" +
                "      }\n" +
                "	   try {\n" +
                "         f2 = null;\n" +
                "      } catch (Throwable t) {\n" +
                "         System.out.println(\"Success\");\n" +
                "      }\n" +
                "	   try {\n" +
                "         f3 = n1;\n" +
                "      } catch (Throwable t) {\n" +
                "         System.out.println(\"Success\");\n" +
                "      }\n" +
                "   }\n" +
                "}\n"
			},
			"Success\n" +
			"Success");
	}
}

