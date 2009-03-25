package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class SetComprehensionTest extends AbstractRegressionTest {
	public static final String WORKSPACE = "..";
	public static final String MODELS_JAR = WORKSPACE + "/jml4-utils/lib/jmlmodelsnonrac.jar";
	public static final String RUNTIME_JAR = WORKSPACE + "/jml4-utils/lib/jmlruntime.jar";

	public SetComprehensionTest(String name) {
		super(name);
	}

	protected String[] getDefaultClassPaths() {
		final String [] superDefaultClassPaths = super.getDefaultClassPaths();
		final int length = superDefaultClassPaths.length;
	    String[] defaultClassPaths = new String[length + 1];
        System.arraycopy(superDefaultClassPaths, 0, defaultClassPaths, 0, length);
        defaultClassPaths[length] = MODELS_JAR;
 //       defaultClassPaths[length + 1] = RUNTIME_JAR;
        return defaultClassPaths;
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

	// tests for various types of reasonably-formatted set comprehensions
	public void test_0001_JMLObjectSet_JMLType_Collection() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLObjectSet {JMLType o | c.contains(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. WARNING in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {JMLType o | c.contains(o) && o != x }).int_size() > 0;\n" +
				"	                                             ^^^^^^^^^^^^^\n" +
				"Type safety: The expression of type Object needs unchecked conversion to conform to JMLType\n" +
				"----------\n");
	}
	public void test_0002_JMLObjectSet_JMLType_JMLObjectSet() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	JMLObjectSet c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLObjectSet {JMLType o | c.has(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. WARNING in X.java (at line 5)\n" +
				"	//@ invariant (new JMLObjectSet {JMLType o | c.has(o) && o != x }).int_size() > 0;\n" +
				"	                                             ^^^^^^^^\n" +
				"Type safety: The expression of type Object needs unchecked conversion to conform to JMLType\n" +
				"----------\n");
	}
	public void test_0003_JMLValueSet_JMLType_JMLObjectSet() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	JMLValueSet c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLValueSet {JMLType o | c.has(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0004_JMLValueSet_JMLType_JMLValueSet() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	JMLValueSet c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLValueSet {JMLType o | c.has(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0005_JMLObjectSet_Object_Collection() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLObjectSet {Object o | c.contains(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0006_JMLObjectSet_Object_JMLObjectSet() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	JMLValueSet c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLObjectSet {Object o | c.has(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0007_JMLValueSet_Object_JMLValueSet() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	JMLValueSet c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLValueSet {Object o | c.has(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 5)\n" +
				"	//@ invariant (new JMLValueSet {Object o | c.has(o) && o != x }).int_size() > 0;\n" + 
				"	                   ^^^^^^^^^^^\n" +
				"Type mismatch: cannot convert from Object to JMLType\n" +
				"----------\n");
	}
	public void test_0008_HashSet_Object_JMLObjectSet() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	JMLObjectSet c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new HashSet {Object o | c.has(o) && o != x }).size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 6)\n" +
				"	//@ invariant (new HashSet {Object o | c.has(o) && o != x }).size() > 0;\n" +
				"	                   ^^^^^^^\n" +
				"Illegal type for set comprehension; JMLObjectSet or JMLValueSet expected.\n" + 
				"----------\n");
	}
	public void test_0020_same_generic_types() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection<String> c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLObjectSet {String o | c.contains(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0021_good_generic_types() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection<String> c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLObjectSet {Object o | c.contains(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0022_bad_generic_types() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection<Integer> c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLObjectSet {String o | c.contains(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. WARNING in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {String o | c.contains(o) && o != x }).int_size() > 0;\n" +
				"	                                            ^^^^^^^^^^^^^\n" +
				"Type safety: The expression of type Integer needs unchecked conversion to conform to String\n" +
				"----------\n");
	}
	
	// tests for unreasonably-formatted set comprehensions
	public void test_0030_bad_boolean_superset_predicate() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection<Integer> c;\n" +
				"   Object x;\n" +
				"	//@ invariant (new JMLObjectSet {Integer o | c.add(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {Integer o | c.add(o) && o != x }).int_size() > 0;\n" +
				"	                                             ^^^^^^^^\n" +
				"Illegal expression for set membership; call to has(o) on JMLValueSet/JMLObjectSet or contains(o) on Collection expected.\n" +
				"----------\n");
	}
	public void test_0031_bad_nonboolean_superset_predicate() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection<Integer> c;\n" +
				"   int x;\n" +
				"	//@ invariant (new JMLObjectSet {Integer o | x++ && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {Integer o | x++ && o != x }).int_size() > 0;\n" + 
				"	                                             ^^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" + 
				"----------\n" +
				"2. ERROR in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {Integer o | x++ && o != x }).int_size() > 0;\n" +
				"	                                             ^^^\n" +
				"Illegal expression for set membership; call to has(o) on JMLValueSet/JMLObjectSet or contains(o) on Collection expected.\n" +
				"----------\n");
	}
	public void test_0032_bad_main_predicate() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection<Integer> c;\n" +
				"   Integer x;\n" +
				"	//@ invariant (new JMLObjectSet {Integer o | c.contains(o) && (o + x) }).int_size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {Integer o | c.contains(o) && (o + x) }).int_size() > 0;\n" +
				"	                                                              ^^^^^^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0033_duplicate_bound_variable() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection<Integer> c;\n" +
				"   Integer x;\n" +
				"	//@ invariant (new JMLObjectSet {Integer x | c.contains(x) && x != null }).int_size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. WARNING in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {Integer x | c.contains(x) && x != null }).int_size() > 0;\n" +
				"	                                         ^\n" +
				"The local variable x is hiding a field from type X\n" +
				"----------\n");
	}
	public void test_0034_multiple_bound_variables() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import java.util.*;\n" + 
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	Collection<Integer> c;\n" +
				"   Integer x;\n" +
				"	//@ invariant (new JMLObjectSet {Integer o, p | c.contains(o) && o != x }).int_size() > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {Integer o, p | c.contains(o) && o != x }).int_size() > 0;\n" +
				"	                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Syntax error on tokens, JmlSetComprehension expected instead\n" +
				"----------\n" +
				"2. ERROR in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {Integer o, p | c.contains(o) && o != x }).int_size() > 0;\n" +
				"	                                              ^\n" +
				"Syntax error on token \"|\", = expected\n" +
				"----------\n" +
				"3. ERROR in X.java (at line 6)\n" +
				"	//@ invariant (new JMLObjectSet {Integer o, p | c.contains(o) && o != x }).int_size() > 0;\n" +
				"	                                                                      ^\n" +
				"Syntax error, insert \";\" to complete BlockStatements\n" +
				"----------\n");
	}
	
	// tests for set comprehensions in method contracts
	public void test_0040_method_contract() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	JMLObjectSet c;\n" +
				"   Object x;\n" +
				"	//@ requires (new JMLObjectSet {Object o | c.has(o) && o != y }).int_size() > 0;\n" +
				"	public void m(Object y) {\n" +
				"		x = y;\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}

	public void test_0041_method_contract_duplicate_bound_variable() {
		this.runNegativeTest( new String[] {
				"X.java",
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n" +
				"	JMLObjectSet c;\n" +
				"   Object x;\n" +
				"	//@ requires (new JMLObjectSet {Object y | c.has(y) && y != x }).int_size() > 0;\n" +
				"	public void m(Object y) {\n" +
				"		x = y;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 5)\n" +
				"	//@ requires (new JMLObjectSet {Object y | c.has(y) && y != x }).int_size() > 0;\n" +
				"	                                       ^\n" +
				"Duplicate local variable y\n" +
				"----------\n");
	}
	
	// basic code generation tests (e.g., make sure nothing breaks when comprehensions are used)
	public void test_0100_codegen_JMLObjectSet() {
		this.runConformTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n"+
				"   public static void main(String[] args) { \n" +
				"   	int i = 0;\n" +
				"       Collection c = new HashSet();" +
				"       try {\n" +
				"   	   int sum = 0;\n" +
				"   	   //@ loop_invariant (new JMLObjectSet {Object o | c.contains(o) && o != null}).int_size() == 0;\n" +
				"   	   while (i < 8) { i++; } \n" +
				"	    } catch (Error e) {\n" +
				"          System.out.println(e.toString());\n" +
				"	    }\n" +
				"	}\n" +
				"}\n"
				});
	}
	public void test_0101_codegen_JMLValueSet() {
		this.runConformTest( new String[] {
				"X.java",
				"import java.util.*;\n" +
				"import org.jmlspecs.models.*;\n" + 
				"public class X {\n"+
				"   public static void main(String[] args) { \n" +
				"   	int i = 0;\n" +
				"       Collection c = new HashSet();" +
				"       try {\n" +
				"   	   int sum = 0;\n" +
				"   	   //@ loop_invariant (new JMLValueSet {JMLType o | c.contains(o) && o != null}).int_size() == 0;\n" +
				"   	   while (i < 8) { i++; } \n" +
				"	    } catch (Error e) {\n" +
				"          System.out.println(e.toString());\n" +
				"	    }\n" +
				"	}\n" +
				"}\n"
				});
	}
}
