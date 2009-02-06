package org.jmlspecs.eclipse.jdt.core.tests.nonnull;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class NNTS_ArrayTestCompiler extends AbstractRegressionTest {

	public NNTS_ArrayTestCompiler(String name) { 
	    super(name);
	}

	// Augment problem detection settings
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
	    Map<String, String> options = super.getCompilerOptions();

	    options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NULLABLE);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.ERROR);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.ERROR);
		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_SpecPath, NullTypeSystemTestCompiler.getSpecPath());
	    return options;
	}

	public void test_0000_Elements() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   /*@nullable*/ String[/*@non_null*/][/*@non_null*/] non_non  = null;\n" +
                "}\n"}, "" );
	}
	public void test_0001_Elements() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   /*@ non_null */ String[/*@non_null*/] non_non  = new String[]{\"hello\"};\n" +
                "   /*@ non_null */ String[/*@nullable*/] non_able = new String[]{\"hello\"};\n" +
                "   /*@ nullable */ String[/*@non_null*/] able_non  = new String[]{\"hello\"};\n" +
                "   /*@ nullable */ String[/*@nullable*/] able_able = null;\n" +
                "}\n" }, "");
	}
	public void test_0002_ElementsInit() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   /*@ non_null */ String[/*@non_null*/] non_non_1 = null;\n" +
                "   /*@ non_null */ String[/*@non_null*/] non_non_2 = new String[]{null};\n" +
                "}\n" }, 
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	/*@ non_null */ String[/*@non_null*/] non_non_1 = null;\n" +
                "	                                      ^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "2. ERROR in X.java (at line 3)\n" +
                "	/*@ non_null */ String[/*@non_null*/] non_non_2 = new String[]{null};\n" +
                "	                                      ^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n");
	}
	public void test_0003_ElementInitField() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   /*@ non_null */ String[/*@non_null*/] non_non = new String[]{\"hello\"};\n" +
                "   /*@ non_null */ String non = non_non[0];\n" +
                "}\n" }, "");
	}
	public void test_0004_ElementAssign() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   /*@ non_null */ String[/*@non_null*/] non_non  = new String[]{\"hello\"};\n" +
                "   /*@ non_null */ String[/*@nullable*/] non_able = new String[]{\"hello\"};\n" +
                "	public void m() {\n"+
                "      /*@ non_null */ String non;\n" +
                "      non = non_non[0];\n" +
                "      non = non_able[0];\n" +
                "   }\n"+
                "}\n" }, 
                "----------\n" +
                "1. ERROR in X.java (at line 7)\n" +
                "	non = non_able[0];\n" +
                "	^^^^^^^^^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n");
	}
	public void test_0005_ElementAssign() {
		this.runNegativeTest(
				new String[] {
					"X.java",
	                "class X {\n" +
	                "   /*@ non_null */ String[/*@non_null*/] non_non  = new String[]{\"hello\"};\n" +
	                "   /*@ non_null */ String[/*@nullable*/] non_able = new String[]{\"hello\"};\n" +
	                "	public void m(/*@ nullable */ String able) {\n"+
	                "      non_non[0]  = able;\n" +
	                "      non_able[0] = able;\n" +
	                "   }\n"+
	                "}\n" }, 
	                "----------\n" +
	                "1. ERROR in X.java (at line 5)\n" +
	                "	non_non[0]  = able;\n" +
	                "	^^^^^^^^^^^^^^^^^^\n" +
	                "Possible assignment of null to an L-value declared non_null\n" +
	                "----------\n");
		}
	public void test_0006_BracketsAfterFieldName() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   String s[];\n" +
                "}\n" }, 
                "");
	}
    public void test_0007_DereferenceField() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class X {\n" +
                "   int i;\n" +
                "   /*@ non_null */ String[/*@non_null*/] non=new String[]{\"hello\"}; //$NON-NLS-1$\n" +
                "   int m1() { return this.non[i].length(); }\n" +
                "}\n"},
                "");
    }
    public void test_0008_VarArgs() {
	    Map<String, String> options = getCompilerOptions();
		options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_Source, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_TargetPlatform, CompilerOptions.VERSION_1_5);
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   void m(Object... args) { }\n" +
                "}\n"},
                "",null,true,options);
    }
    public void test_0009_VarArgsArray() {
	    Map<String, String> options = getCompilerOptions();
		options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_Source, CompilerOptions.VERSION_1_5);
		options.put(CompilerOptions.OPTION_TargetPlatform, CompilerOptions.VERSION_1_5);
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   void m(Object[]... args) { }\n" +
                "}\n"},
                "",null,true,options);
    }
    public void test_0010_splitParam() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   void m(Object[] p[]) { }\n" +
                "}\n"},
                "");
    }
    public void test_0011_splitLocal() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   public static void main(String[] args) {\n" +
                "      String[][] s[] = null;\n" +
                "   }\n" +
                "}\n"},
                "");
    }
    public void test_0012_splitField() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "class X {\n" +
	            "   String[][] s[] = null;\n" +
	            "}\n"},
	            "");
	}
	public void test_0013_2d_fieldAssignment() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   /*@ non_null */ String[/*@non_null*/][/*@non_null*/] non_non;\n" +
                "   /*@ non_null */ String[/*@non_null*/][/*@nullable*/] non_able;\n" +
                "   /*@ non_null */ String[/*@nullable*/][/*@non_null*/] able_non;\n" +
                "   /*@ non_null */ String[/*@nullable*/][/*@nullable*/] able_able;\n" +
                "   public X() {\n" +
                "	non_non = null;\n" + //error 7
                "	non_non = new String[][]{{\"hello\"}};\n" +
                "	non_non[0] = null;\n" + //error 9
                "	non_non[0] = new String[]{\"hello\"};\n" +
                "	non_non[0][0] = null;\n" + //error 11
                "	non_non[0][0] = \"hello\";\n" +
                "\n" +
                "	non_able = new String[][]{{\"hello\"}};\n" +
                "	non_able[0] = null;\n" +//error 15
                "	non_able[0] = new String[]{\"hello\"};\n" +
                "	non_able[0][0] = null;\n" +
                "	non_able[0][0] = \"hello\";\n" +
                "\n" +
                "	able_non = new String[][]{{\"hello\"}};\n" +
                "	able_non[0] = null;\n" +
                "	able_non[0] = new String[]{\"hello\"};\n" +
                "	able_non[0][0] = null;\n" +//error 23
                "	able_non[0][0] = \"hello\";\n" +
                "\n" +
                "	able_able = new String[][]{{\"hello\"}};\n" +
                "	able_able[0] = null;\n" +
                "	able_able[0] = new String[]{\"hello\"};\n" +
                "	able_able[0][0] = null;\n" +
                "	able_able[0][0] = \"hello\";\n" +
                "	}\n" +
				"}\n" }, 
				"----------\n" + 
				"1. ERROR in X.java (at line 7)\n" + 
				"	non_non = null;\n" + 
				"	^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 9)\n" + 
				"	non_non[0] = null;\n" + 
				"	^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 11)\n" + 
				"	non_non[0][0] = null;\n" + 
				"	^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 15)\n" + 
				"	non_able[0] = null;\n" + 
				"	^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 23)\n" + 
				"	able_non[0][0] = null;\n" + 
				"	^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 23)\n" + 
				"	able_non[0][0] = null;\n" + 
				"	^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"7. ERROR in X.java (at line 24)\n" + 
				"	able_non[0][0] = \"hello\";\n" + 
				"	^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"8. ERROR in X.java (at line 29)\n" + 
				"	able_able[0][0] = null;\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"9. ERROR in X.java (at line 30)\n" + 
				"	able_able[0][0] = \"hello\";\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n");
	}
	public void _test_0014_2d_fieldAssignment_initializers() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   /*@ non_null */ String[/*@non_null*/][/*@non_null*/] non_non   = new String[2][2];\n" +
                "   /*@ non_null */ String[/*@non_null*/][/*@nullable*/] non_able  = new String[2][2];\n" +
                "   /*@ non_null */ String[/*@nullable*/][/*@non_null*/] able_non  = new String[2][2];\n" +
                "   /*@ non_null */ String[/*@nullable*/][/*@nullable*/] able_able = new String[2][2];\n" +
                "   public void m() {\n" +
                "	non_non = new String[][]{null};\n" + //error 8
                "	non_non = new String[][]{{null}};\n" + //error 9
                "	}\n" +
				"}\n" }, 
                "2 errors");
	}
	public void test_0015_2d_localAssignment() {
		this.runNegativeTest(
			new String[] {
				"X.java",
                "class X {\n" +
                "   public void m() {\n" +
                "   /*@ non_null */ String[/*@non_null*/][/*@non_null*/] non_non;\n" +
                "   /*@ non_null */ String[/*@non_null*/][/*@nullable*/] non_able;\n" +
                "   /*@ non_null */ String[/*@nullable*/][/*@non_null*/] able_non;\n" +
                "   /*@ non_null */ String[/*@nullable*/][/*@nullable*/] able_able;\n" +
                "	non_non = null;\n" + //error 7
                "	non_non = new String[][]{{\"hello\"}};\n" +
                "	non_non[0] = null;\n" + //error 9
                "	non_non[0] = new String[]{\"hello\"};\n" +
                "	non_non[0][0] = null;\n" + //error 11
                "	non_non[0][0] = \"hello\";\n" +
                "\n" +
                "	non_able = new String[][]{{\"hello\"}};\n" +
                "	non_able[0] = null;\n" +//error 15
                "	non_able[0] = new String[]{\"hello\"};\n" +
                "	non_able[0][0] = null;\n" +
                "	non_able[0][0] = \"hello\";\n" +
                "\n" +
                "	able_non = new String[][]{{\"hello\"}};\n" +
                "	able_non[0] = null;\n" +
                "	able_non[0] = new String[]{\"hello\"};\n" +
                "	able_non[0][0] = null;\n" +//error 23
                "	able_non[0][0] = \"hello\";\n" +
                "\n" +
                "	able_able = new String[][]{{\"hello\"}};\n" +
                "	able_able[0] = null;\n" +
                "	able_able[0] = new String[]{\"hello\"};\n" +
                "	able_able[0][0] = null;\n" +
                "	able_able[0][0] = \"hello\";\n" +
                "	}\n" +
				"}\n" }, 
				"----------\n" + 
				"1. ERROR in X.java (at line 7)\n" + 
				"	non_non = null;\n" + 
				"	^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 9)\n" + 
				"	non_non[0] = null;\n" + 
				"	^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 11)\n" + 
				"	non_non[0][0] = null;\n" + 
				"	^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 15)\n" + 
				"	non_able[0] = null;\n" + 
				"	^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 23)\n" + 
				"	able_non[0][0] = null;\n" + 
				"	^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 23)\n" + 
				"	able_non[0][0] = null;\n" + 
				"	^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"7. ERROR in X.java (at line 24)\n" + 
				"	able_non[0][0] = \"hello\";\n" + 
				"	^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"8. ERROR in X.java (at line 29)\n" + 
				"	able_able[0][0] = null;\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"9. ERROR in X.java (at line 30)\n" + 
				"	able_able[0][0] = \"hello\";\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n");
	}
	// PC: I don't understand the following test ... because the 
	// nullity annotations in the .jml file explicitly match those
	// given here in the source.  I assume this is an error
	// (otherwise, what is the point of having the test read "FromSpec"?
	public void test_0016_arrayReturnTypeNullityFromSpec() {
		this.runNegativeTest(
			new String[] {
				"X0016.java",
                "public class X0016 {\n" +
                "   static { \n" +
                "		X0016 x = new X0016();\n" +
                "		/*@non_null*/ String s = x.toNonNullStr(); // Ok\n" +
                "		/*@non_null*/ String sanity = x.toNullableStr();	// Error\n" +
                "		x.m(x.toCharArray());	// Ok\n" +
                "	}\n" +
                "   /*@non_null*/ char[] toCharArray() { return new char[0]; };\n" +
                "   /*@non_null*/ String toNonNullStr() { return \"\"; };\n" +
                "   /*@nullable*/ String toNullableStr() { return null; };\n" +
                "   void m(/*@non_null*/ char[] cc) {}\n" +
                "}\n"},
                "----------\n" +
                "1. ERROR in X0016.java (at line 5)\n" +
                "	/*@non_null*/ String sanity = x.toNullableStr();	// Error\n" +
                "	                     ^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n");
    }

	public void test_0016b_nullityMismatchFromSpec() {
		this.runNegativeTest(
			new String[] {
				"X0016.java",
                "public class X0016 {\n" +
                "   /*@non_null*/ char[] toCharArray() { return new char[0]; };\n" +
                "   /*@nullable*/ String toNonNullStr() { return \"\"; };\n" +
                "   /*@nullable*/ String toNullableStr() { return null; };\n" +
                "   void m(/*@non_null*/ char[] cc) {}\n" +
                "}\n"},
        		"----------\n" + 
        		"1. WARNING in X0016.java (at line 3)\n" + 
        		"	/*@nullable*/ String toNonNullStr() { return \"\"; };\n" + 
        		"	                     ^^^^^^^^^^^^^^\n" + 
        		"Nullity of declaration is different in specification file (non_null)\n" + 
                "----------\n");
    }

	public void test_0017_ArrayReceiverIsCast() {
	    Map<String, String> options = getCompilerOptions();
	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NON_NULL);
		this.runNegativeTest(
			new String[] {
				"X0017.java",
                "public class X0017 {\n" +
                "	int[] buf1 = new int[0];\n" +
                "	/*@nullable*/int[] buf2 = new int[0];\n" +
                "	/*@non_null*/int[] buf3 = new int[0];\n" +
                "   int m0(/*@nullable*/ int[] ia) { return (/*+@(non_null)*/ia)[0]; }\n" +
                "   int m1() { return (/*+@(non_null)*/buf1)[0]; }\n" +
                "   int m2() { return (/*+@(non_null)*/buf2)[0]; }\n" +
                "   int m3() { return (/*+@(non_null)*/buf3)[0]; }\n" +
                "}\n"},
                "",null,true,options);
    }

	/**
	 * Local variables of array types are much like fields in
	 * that the value of the array elements could be changed
	 * by another thread (this is impossible for scalar
	 * local variables).
	 * Hence, in general, flow analysis cannot determine statically
	 * with full certainty the nullity status of array elements.
	 * Thus, this means that the user should explicitly provide
	 * nullity modifiers for array elements in array declarations.
	 * Otherwise, the compiler default will be applied.
	 */
	public void _test_0018_NonNullDefaultAndLocalArray() {
		// Non-null default applies to array elements
		// of local array variables.
	    Map<String, String> options = getCompilerOptions();
	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NON_NULL);
		this.runNegativeTest(
			new String[] {
				"X0018.java",
                "public class X0018 {\n" +
                "	void m() {\n" +
                "		// oa implicitly declared with non-null elements\n" +
                "		Object oa[] = new Object[1]; // should be an error\n" +
                "		oa[0] = null; // error\n" +
                "		Object oa2[] = new Object[] { new Integer(1) }; // ok\n" +
                "		Object oa3[/*@nullable*/] = new Object[1]; // ok\n" +
                "		oa3[0] = null; // ok\n" +
                "	}\n" +
                "}\n"},
                "----------\n" +
                "1. ERROR in X0018.java (at line 4)\n" +
                "	Object oa[] = new Object[1]; // should be an error\n" +
                "	              ^^^^^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "2. ERROR in X0018.java (at line 5)\n" +
                "	oa[0] = null; // error\n" +
                "	^^^^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n"
                ,null,true,options);
    }
}
