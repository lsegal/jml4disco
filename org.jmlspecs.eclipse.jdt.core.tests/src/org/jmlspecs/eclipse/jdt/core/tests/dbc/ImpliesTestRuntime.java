package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class ImpliesTestRuntime extends AbstractRegressionTest {

	public ImpliesTestRuntime(String name) {
		super(name);
	}

	// Augment problem detection settings
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
	    Map<String, String> options = super.getCompilerOptions();

	    options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NULLABLE);
	    options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.ENABLED);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_SpecPath, DbcTestCompiler.getSpecPath());
	    return options;
	}

	public void test_0001_sanity() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
                "	public static void main(String[] args) {\n" +
                "		//@ assert true ==> true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0002_implies() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
                "	public static void main(String[] args) {\n" +
                "		//@ assert (true  ==> true)  == true;\n" +
                "		//@ assert (true  ==> false) == false;\n" +
                "		//@ assert (false ==> true)  == true;\n" +
                "		//@ assert (false ==> false) == true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0003_rev_implies() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
                "	public static void main(String[] args) {\n" +
                "		//@ assert (true  <== true)  == true;\n" +
                "		//@ assert (true  <== false) == true;\n" +
                "		//@ assert (false <== true)  == false;\n" +
                "		//@ assert (false <== false) == true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0004_equiv() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
                "	public static void main(String[] args) {\n" +
                "		//@ assert (true  <==> true)  == true;\n" +
                "		//@ assert (true  <==> false) == false;\n" +
                "		//@ assert (false <==> true)  == false;\n" +
                "		//@ assert (false <==> false) == true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0005_not_equiv() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
                "	public static void main(String[] args) {\n" +
                "		//@ assert (true  <=!=> true)  == false;\n" +
                "		//@ assert (true  <=!=> false) == true;\n" +
                "		//@ assert (false <=!=> true)  == true;\n" +
                "		//@ assert (false <=!=> false) == false;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0006_implies() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   public static boolean b(boolean l, boolean r) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l ==> r); */\n" +
				"       return result;\n" +
				"   }\n" +
                "	public static void main(String[] args) {\n" +
                "		//@ assert b(true,  true)  == true;\n" +
                "		//@ assert b(true,  false) == false;\n" +
                "		//@ assert b(false, true)  == true;\n" +
                "		//@ assert b(false, false) == true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0007_rev_implies() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   public static boolean b(boolean l, boolean r) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l <== r); */\n" +
				"       return result;\n" +
				"   }\n" +
                "	public static void main(String[] args) {\n" +
                "		//@ assert b(true,  true)  == true;\n" +
                "		//@ assert b(true,  false) == true;\n" +
                "		//@ assert b(false, true)  == false;\n" +
                "		//@ assert b(false, false) == true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0008_equiv() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   public static boolean b(boolean l, boolean r) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l <==> r); */\n" +
				"       return result;\n" +
				"   }\n" +
                "	public static void main(String[] args) {\n" +
                "		//@ assert b(true,  true)  == true;\n" +
                "		//@ assert b(true,  false) == false;\n" +
                "		//@ assert b(false, true)  == false;\n" +
                "		//@ assert b(false, false) == true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0009_not_equiv() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   public static boolean b(boolean l, boolean r) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l <=!=> r); */\n" +
				"       return result;\n" +
				"   }\n" +
                "	public static void main(String[] args) {\n" +
                "		//@ assert b(true,  true)  == false;\n" +
                "		//@ assert b(true,  false) == true;\n" +
                "		//@ assert b(false, true)  == true;\n" +
                "		//@ assert b(false, false) == false;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0010_implies() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   public static boolean b_true(boolean l) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l ==> true); */\n" +
				"       return result;\n" +
				"   }\n" +
				"   public static boolean b_false(boolean l) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l ==> false); */\n" +
				"       return result;\n" +
				"   }\n" +
                "	public static void main(String[] args) {\n" +
                "		//@ assert b_true(true)   == true;\n" +
                "		//@ assert b_true(false)  == true;\n" +
                "		//@ assert b_false(true)  == false;\n" +
                "		//@ assert b_false(false) == true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0011_rev_implies() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   public static boolean b_true(boolean l) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l <== true); */\n" +
				"       return result;\n" +
				"   }\n" +
				"   public static boolean b_false(boolean l) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l <== false); */\n" +
				"       return result;\n" +
				"   }\n" +
                "	public static void main(String[] args) {\n" +
                "		//@ assert b_true(true)   == true;\n" +
                "		//@ assert b_true(false)  == false;\n" +
                "		//@ assert b_false(true)  == true;\n" +
                "		//@ assert b_false(false) == true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0012_equiv() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   public static boolean b_true(boolean l) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l <==> true); */\n" +
				"       return result;\n" +
				"   }\n" +
				"   public static boolean b_false(boolean l) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l <==> false); */\n" +
				"       return result;\n" +
				"   }\n" +
                "	public static void main(String[] args) {\n" +
                "		//@ assert b_true(true)   == true;\n" +
                "		//@ assert b_true(false)  == false;\n" +
                "		//@ assert b_false(true)  == false;\n" +
                "		//@ assert b_false(false) == true;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0013_not_equiv() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   public static boolean b_true(boolean l) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l <=!=> true); */\n" +
				"       return result;\n" +
				"   }\n" +
				"   public static boolean b_false(boolean l) {\n" +
				"       boolean result = false;\n" +
				"       /*@ result = (l <=!=> false); */\n" +
				"       return result;\n" +
				"   }\n" +
                "	public static void main(String[] args) {\n" +
                "		//@ assert b_true(true)   == false;\n" +
                "		//@ assert b_true(false)  == true;\n" +
                "		//@ assert b_false(true)  == true;\n" +
                "		//@ assert b_false(false) == false;\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
}
