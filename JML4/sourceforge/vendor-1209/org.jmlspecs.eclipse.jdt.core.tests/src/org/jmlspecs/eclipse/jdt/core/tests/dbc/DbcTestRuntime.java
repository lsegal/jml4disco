package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class DbcTestRuntime extends AbstractRegressionTest {

	public DbcTestRuntime(String name) {
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
                "		//@ assert true;\n" +
                "       int count = 0;\n" +
                "       try {\n" +
                "		//@ assert false;\n" +
                "       } catch (Throwable t) {\n" +
                "       	count++;\n" +
                "       System.out.println(\"Count is \"+count);\n" +
                "       }\n" +
                "	}\n" +
                "}\n"
			   },
                "Count is 1");
	}
 
	public void test_0002_simple_method_spec() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ requires true;\n" +
				"   //@ ensures true;\n" +
                "	public static void main(String[] args) {\n" +
                "       System.out.println(\"Done.\");\n" +
                "	}\n" +
                "}\n"
			   },
                "Done.");
	}

	public void test_0003_method_spec_mult_requires() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ requires true;\n" +
				"   //@ requires true;\n" +
				"   //@ ensures true;\n" +
                "	public static void main(String[] args) {\n" +
                "       System.out.println(\"Done.\");\n" +
                "	}\n" +
                "}\n"
			   },
                "Done.");
	}
 
	public void test_0004_method_spec_mult_ensures() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ requires true;\n" +
				"   //@ ensures true;\n" +
				"   //@ ensures true;\n" +
                "	public static void main(String[] args) {\n" +
                "       System.out.println(\"Done.\");\n" +
                "	}\n" +
                "}\n"
			   },
                "Done.");
	}
	public void test_0005_method_spec_parm_in_ensures() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ requires true;\n" +
				"   //@ ensures true;\n" +
				"   //@ ensures args != null;\n" +
                "	public static void main(String[] args) {\n" +
                "       System.out.println(\"Done.\");\n" +
                "	}\n" +
                "}\n"
			   },
                "Done.");
	}
	public void test_0006_method_spec_only_req() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ requires true;\n" +
                "	public static void main(String[] args) {\n" +
                "       System.out.println(\"Done.\");\n" +
                "	}\n" +
                "}\n"
			   },
                "Done.");
	}
	public void test_0007_method_spec_only_ens() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ ensures true;\n" +
                "	public static void main(String[] args) {\n" +
                "       System.out.println(\"Done.\");\n" +
                "	}\n" +
                "}\n"
			   },
                "Done.");
	}
	public void test_0008_method_spec_checkPre() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ requires false;\n" +
                "	public void m() {\n" +
                "	}\n" +
                "	public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "          System.out.println(\"Done.\");\n" +
                "       }\n" +
                "	}\n" +
                "}\n"
			   },
                "Done.");
	}
	public void test_0009_method_spec_checkPost() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ ensures false;\n" +
                "	public void m() {\n" +
                "	}\n" +
                "	public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "          System.out.println(\"Done.\");\n" +
                "       }\n" +
                "	}\n" +
                "}\n"
			   },
                "Done.");
	}
}
