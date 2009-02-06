package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class SubtypeExpressionTest extends AbstractRegressionTest {

	public SubtypeExpressionTest(String name) {
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
		options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.versionFromJdkLevel(ClassFileConstants.JDK1_5));
		options.put(CompilerOptions.OPTION_Source, CompilerOptions.versionFromJdkLevel(ClassFileConstants.JDK1_5));
		options.put(CompilerOptions.OPTION_TargetPlatform, CompilerOptions.versionFromJdkLevel(ClassFileConstants.JDK1_5));
		return options;
	}

	// tests for various reasonably-formatted subtype expressions
	public void test_0001_Valid() {
		runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		//@ assert Collection.class <: Object.class;\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}
	public void test_0002_ValidWithObjects() {
		runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Class a = Collection.class;\n" + 
				"		Class b = Object.class;\n" + 
				"		//@ assert a <: b;\n" +
				"	}\n" +
				"}\n"
				},
				"");		
	}
	public void test_0003_ValidWithMethods() {
		runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Collection c = new HashSet();\n" + 
				"		Object o = new Object();\n" + 
				"		//@ assert c.getClass() <: o.getClass();\n" +
				"	}\n" +
				"}\n"
				},
				"");		
	}
	// the following two tests will not work until code generation for \type and \typeof is fixed
	public void _test_0004_ValidWithTypes() {
		runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		//@ assert \\type(Collection) <: \\type(Object);\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}	
	public void _test_0005_ValidWithTypeofs() {
		runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Collection c = new HashSet();\n" +
				"		Object o = new Object();\n" + 
				"		//@ assert \\typeof(c) <: \\typeof(o);\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}
	// various tests for invalid subtype expressions
	public void test_0020_InvalidBoth() {
		runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Object o1 = null;\n" + 
				"		Object o2 = null;\n" + 
				"		//@ assert o1 <: o2;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 5)\n" +
				"	//@ assert o1 <: o2;\n" +
				"	           ^^\n" +
				"Type mismatch: cannot convert from Object to Class<T>\n" +
				"----------\n" +
				"2. ERROR in X.java (at line 5)\n" +
				"	//@ assert o1 <: o2;\n" +
				"	                 ^^\n" +
				"Type mismatch: cannot convert from Object to Class<T>\n" +
				"----------\n");
	}
	public void test_0021_InvalidLeft() {
		runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Object o1 = null;\n" + 
				"		Class o2 = null;\n" + 
				"		//@ assert o1 <: o2;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 5)\n" +
				"	//@ assert o1 <: o2;\n" +
				"	           ^^\n" +
				"Type mismatch: cannot convert from Object to Class<T>\n" +
				"----------\n");
	}	
	public void test_0022_InvalidRight() {
		runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Class o1 = null;\n" + 
				"		Object o2 = null;\n" + 
				"		//@ assert o1 <: o2;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 5)\n" +
				"	//@ assert o1 <: o2;\n" +
				"	                 ^^\n" +
				"Type mismatch: cannot convert from Object to Class<T>\n" +
				"----------\n");
	}	
	public void test_0023_InvalidWithNull() {
		runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Class o1 = null;\n" +  
				"		//@ assert o1 <: null;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 4)\n" +
				"	//@ assert o1 <: null;\n" +
				"	                 ^^^^\n" +
				"Type mismatch: cannot convert from null to Class<T>\n" +
				"----------\n");
	}
	public void test_0024_InvalidOutsideJMLClause() {
		runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Class o1 = null;\n" +
				"		Class o2 = null;\n" +
				"		if (o1 <: o2) {\n" +
				"		}\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" + 
				"1. ERROR in X.java (at line 5)\n" + 
				"	if (o1 <: o2) {\n" + 
				"	       ^^\n" + 
				"Syntax error on tokens, they can be merge to form <:\n" + 
				"----------\n");
	}
	
	// basic code generation tests 
	public void test_0101_codegen_True() {
		runConformTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		//@ assert Collection.class <: Object.class;\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}
	public void test_0102_codegen_TrueWithObjects() {
		runConformTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Class a = Collection.class;\n" + 
				"		Class b = Object.class;\n" + 
				"		//@ assert a <: b;\n" +
				"	}\n" +
				"}\n"
				},
				"");		
	}
	public void test_0103_codegen_TrueWithMethods() {
		runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Collection c = new HashSet();\n" + 
				"		Object o = new Object();\n" + 
				"		//@ assert c.getClass() <: o.getClass();\n" +
				"	}\n" +
				"}\n"
				},
				"");		
	}
	// the following two tests will not work until code generation for \type and \typeof works
	public void _test_0104_codegen_TrueWithTypes() {
		runConformTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		//@ assert \\type(Collection) <: \\type(Object);\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}
	public void _test_0105_codegen_TrueWithTypeofs() {
		runConformTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		Collection c = new HashSet();\n" +
				"		Object o = new Object();\n" + 
				"		//@ assert \\typeof(c) <: \\typeof(o);\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}

	public void test_0110_codegen_Reflexive() {
		runConformTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		//@ assert Boolean.TYPE <: Boolean.TYPE;\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}
	public void test_0111_codegen_False() {
		runConformTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"public class X {\n" +
				"	public static void main(String[] args) {\n" +
				"		//@ assert !(Object.class <: Collection.class);\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}
}
