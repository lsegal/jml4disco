package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class QuantifierTest extends AbstractRegressionTest {

	public QuantifierTest(String name) {
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
		return options;
	}

	// tests for boolean-type boolean-body quantifiers (forall, exists)
	public void test_0001_forall_no_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i; 0 < i);\n" +
				"}\n"
				},
				"");
	}
	public void test_0002_forall() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i; 0 < i; 0 < i);\n" +
				"}\n"
				},
				"");
	}
	public void test_0003_forall_no_range_multi_vars() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i, j, k; (i < j && j < k) || !(i < k) );\n" +
				"}\n"
				},
				"");
	}
	public void test_0004_forall_multi_vars() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i, j, k; i < j && j < k; i < k);\n" +
				"}\n"
				},
				"");
	}
	public void test_0005_forall_no_range_bad_body() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i; 27);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall int i; 27);\n" +
				"	                              ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0006_forall_bad_body() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i; 0 < i; 27);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall int i; 0 < i; 27);\n" +
				"	                                     ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0007_forall_bad_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i; 27; 0 < i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall int i; 27; 0 < i);\n" +
				"	                              ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0008_forall_bad_both() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i; 27; 8);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall int i; 27; 8);\n" +
				"	                              ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n" +
				"2. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall int i; 27; 8);\n" +
				"	                                  ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0009_exists() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\exists int i; 0 < i);\n" +
				"}\n"
				},
				"");
	}
	
	// tests for long-type boolean-body quantifier (num_of)
	public void test_0010_num_of_type() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\num_of int i; 0 < i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\num_of int i; 0 < i);\n" +
				"	              ^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Type mismatch: cannot convert from long to boolean\n" +
				"----------\n");
	}
	public void test_0011_num_of_no_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\num_of int i; 0 < i) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0012_num_of() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\num_of int i; 0 < i; 0 < i) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0013_num_of_no_range_multi_vars() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\num_of int i, j, k; (i < j && j < k) || !(i < k) ) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0014_num_of_multi_vars() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\num_of int i, j, k; i < j && j < k; i < k) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0015_num_of_no_range_bad_body() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\num_of int i; 27) > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\num_of int i; 27) > 0;\n" +
				"	                              ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0016_num_of_bad_body() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\num_of int i; 0 < i; 27) > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\num_of int i; 0 < i; 27) > 0;\n" +
				"	                                     ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0017_num_of_bad_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\num_of int i; 27; 0 < i) > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\num_of int i; 27; 0 < i) > 0;\n" +
				"	                              ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0018_num_of_bad_both() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\num_of int i; 27; 8) > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\num_of int i; 27; 8) > 0;\n" +
				"	                              ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n" +
				"2. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\num_of int i; 27; 8) > 0;\n" +
				"	                                  ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	
	// tests for body-type numeric-body quantifiers (\sum, \product, \min, \max)
	public void test_0020_max_type_byte() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max byte i; 0 < i; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max byte i; 0 < i; i);\n" +
				"	              ^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Type mismatch: cannot convert from byte to boolean\n" +
				"----------\n");
	}
	public void test_0021_max_type_char() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max char i; 0 < i; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max char i; 0 < i; i);\n" +
				"	              ^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Type mismatch: cannot convert from char to boolean\n" +
				"----------\n");
	}
	public void test_0022_max_type_short() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max short i; 0 < i; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max short i; 0 < i; i);\n" +
				"	              ^^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Type mismatch: cannot convert from short to boolean\n" +
				"----------\n");
	}
	public void test_0023_max_type_int() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max int i; 0 < i; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max int i; 0 < i; i);\n" +
				"	              ^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0024_max_type_long() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max long i; 0 < i; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max long i; 0 < i; i);\n" +
				"	              ^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Type mismatch: cannot convert from long to boolean\n" +
				"----------\n");
	}
	public void test_0025_max_type_float() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max float i; 0 < i; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max float i; 0 < i; i);\n" +
				"	              ^^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Type mismatch: cannot convert from float to boolean\n" +
				"----------\n");
	}
	public void test_0026_max_type_double() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max double i; 0 < i; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max double i; 0 < i; i);\n" +
				"	              ^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Type mismatch: cannot convert from double to boolean\n" +
				"----------\n");
	}
	public void test_0027_max_no_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max int i; i) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0028_max() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max int i; 0 < i; i) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0029_max_no_range_multi_vars() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max int i, j, k; i * j + k) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0030_max_multi_vars() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max int i, j, k; i < j && j < k; i * j + k) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0031_max_no_range_bad_body() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max int i; true) > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max int i; true) > 0;\n" +
				"	                           ^^^^\n" +
				"Type mismatch: cannot convert from boolean to double\n" +
				"----------\n");
	}
	public void test_0032_max_bad_body() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max int i; 0 < i; true) > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max int i; 0 < i; true) > 0;\n" +
				"	                                  ^^^^\n" +
				"Type mismatch: cannot convert from boolean to double\n" +
				"----------\n");
	}
	public void test_0033_max_bad_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max int i; 27; i) > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max int i; 27; i) > 0;\n" +
				"	                           ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}
	public void test_0034_max_bad_both() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\max int i; 27; true) > 0;\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max int i; 27; true) > 0;\n" +
				"	                           ^^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n" +
				"2. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\max int i; 27; true) > 0;\n" +
				"	                               ^^^^\n" +
				"Type mismatch: cannot convert from boolean to double\n" +
				"----------\n");
	}
	public void test_0035_min() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\min int i; 0 < i; i) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0036_product() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\product int i; 0 < i; i) > 0;\n" +
				"}\n"
				},
				"");
	}
	public void test_0037_sum() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\sum int i; 0 < i; i) > 0;\n" +
				"}\n"
				},
				"");
	}
	
	// tests for multiple quantifiers (noninterference of scopes)
	public void test_0040_two_quantifiers() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i, j; 0 < i && i < j; j > i);\n" +
				"	//@ invariant (\\forall int i, k; 0 < i && i < k; k > i);\n" +
				"}\n"
				},
				"");
	}

	// tests for degenerate quantifier syntax
	public void test_0045_empty_range_syntax() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i, j; ; j > i);\n" +
				"}\n"
				},
				"");		
	}

	// tests for quantifiers in method contracts
	public void test_0050_method_contract() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ pre (\\forall int i; 0 < i; i > 0);\n" +
				"	public void a() {\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}
	
	// tests for nested quantifiers
	public void test_0060_nested_no_ranges() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i; (\\exists int j; j <= i));\n" +
				"}\n"
				},
				"");
	}
	public void test_0061_nested_no_outer_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i; (\\exists int j; j <= i; j < 27));\n" +
				"}\n"
				},
				"");
	}
	public void test_0062_nested_no_inner_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int i; 0 < i; (\\exists int j; j <= i));\n" +
				"}\n"
				},
				"");
	}
	
	// tests for reference types
	public void test_0070_reference_type_no_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall Object i; i != null);\n" +
				"}\n"
				},
				"");
	}
	public void test_0071_reference_type() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall Object i; i != null; i != null);\n" +
				"}\n"
				},
				"");
	}
	public void test_0071_reference_type_bad_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall Object i; i != null; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall Object i; i != null; i);\n" +
				"	                                            ^\n" +
				"Type mismatch: cannot convert from Object to boolean\n" + 
				"----------\n");
	}
	
	// tests for array types
	public void test_0080_array_type_no_range() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall Object[] i; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall Object[] i; i);\n" +
				"	                                   ^\n" +
				"Type mismatch: cannot convert from Object[] to boolean\n" + 
				"----------\n");
	}
	public void test_0081_array_type() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall Object[] i; i != null; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall Object[] i; i != null; i);\n" +
				"	                                              ^\n" +
				"Type mismatch: cannot convert from Object[] to boolean\n" + 
				"----------\n");
	}
	public void test_0082_array_type_multi_dim() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall Object[][][] i; i != null; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall Object[][][] i; i != null; i);\n" +
				"	                                                  ^\n" +
				"Type mismatch: cannot convert from Object[][][] to boolean\n" + 
				"----------\n");
	}
	public void test_0082_array_type_split_dim() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall Object[][] i[][]; i != null; i);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall Object[][] i[][]; i != null; i);\n" +
				"	                                                    ^\n" +
				"Type mismatch: cannot convert from Object[][][][] to boolean\n" + 
				"----------\n");
	}
	public void test_0083_array_type_split_dim_multi_var() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall Object[][] i[][], j[]; i; j);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall Object[][] i[][], j[]; i; j);\n" +
				"	                                              ^\n" +
				"Type mismatch: cannot convert from Object[][][][] to boolean\n" + 
				"----------\n" +
				"2. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall Object[][] i[][], j[]; i; j);\n" +
				"	                                                 ^\n" +
				"Type mismatch: cannot convert from Object[][][] to boolean\n" + 
				"----------\n");
	}
	
	// tests for quantifiers that generate hiding or unresolved warnings and errors
	public void test_0090_hiding_instance_field() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	private int i;\n" +
				"	//@ invariant (\\forall int i; 0 < i);\n" +
				"	public void a() {\n" +
				"		i = i + 1;\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. WARNING in X.java (at line 3)\n" +
				"	//@ invariant (\\forall int i; 0 < i);\n" +
				"	                           ^\n" +
				"The local variable i is hiding a field from type X\n" +
				"----------\n");
	}
	public void test_0091_duplicate_bound_var() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" + 
				"	//@ invariant (\\forall int i, i; i < 8; i < 27);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall int i, i; i < 8; i < 27);\n" +
				"	                              ^\n" +
				"Duplicate local variable i\n" +
				"----------\n");
	}
	public void test_0092_nested_duplicate_bound_var() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" + 
				"	//@ invariant (\\forall int i; 0 < i; (\\exists int i; i < 27; 8 < i));\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall int i; 0 < i; (\\exists int i; i < 27; 8 < i));\n" +
				"	                                                  ^\n" +
				"Duplicate local variable i\n" +
				"----------\n");
	}
	public void test_0093_duplicate_local_var() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	public void a() {\n" +
				"		int i;\n" +
				"		//@ assert (\\forall int i; 0 < i);\n" +
				"	}\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 4)\n" +
				"	//@ assert (\\forall int i; 0 < i);\n" +
				"	                        ^\n" +
				"Duplicate local variable i\n" +
				"----------\n");
	}

	public void test_0094_unresolved_var() {
		this.runNegativeTest( new String[] {
				"X.java",
				"public class X {\n" +
				"	//@ invariant (\\forall int a, b; 0 < a && a < b && c);\n" +
				"}\n"
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant (\\forall int a, b; 0 < a && a < b && c);\n" +
				"	                                                   ^\n" +
				"c cannot be resolved\n" +
				"----------\n");
	}
	// basic code generation tests (e.g., make sure nothing breaks when quantifiers are used)
    public void test_0100_codegen_boolean() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "       try {\n" +
                "   	   int sum = 0;\n" +
                "   	   //@ loop_invariant (\\forall int j; j == 0; j == 0);\n" +
                "   	   while (i < 8) { i++; } \n" +
                "	    } catch (Error e) {\n" +
                "          System.out.println(e.toString());\n" +
                "	    }\n" +
                "	}\n" +
                "}\n"
                },
        		"");
    }
    public void test_0101_codegen_numeric() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   public static void main(String[] args) { \n" +
                "   	int i = 0;\n" +
                "       try {\n" +
                "   	   int sum = 0;\n" +
                "   	   //@ loop_invariant (\\sum int j; j == 0; j) == 0;\n" +
                "   	   while (i < 8) { i++; } \n" +
                "	    } catch (Error e) {\n" +
                "          System.out.println(e.toString());\n" +
                "	    }\n" +
                "	}\n" +
                "}\n"
                },
        		"");
    }

    public void _test_9000_boundVarInMethodBody() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
				"	//@ requires (\\forall int i; 1 < i; i < i * i);\n" +
				"	public void a(int j) {\n" +
				"		int i = j;\n" +
                "	}\n" +
                "}\n"
                },
        		"");
    }
}
