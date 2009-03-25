package org.jmlspecs.eclipse.jdt.core.tests.nonnull;

import java.io.File;
import java.io.IOException;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.eclipse.jdt.core.tests.util.JmlCoreTestsUtil;
import org.jmlspecs.eclipse.jdt.core.tests.util.JmlTestCase;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class NullTypeSystemTestCompiler extends JmlTestCase {

	public NullTypeSystemTestCompiler(String name) { 
	    super(name);
	}

	// Augment problem detection settings
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
	    Map<String, String> options = super.getCompilerOptions();

	    options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NULLABLE);
	    options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.DISABLED);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.ERROR);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.ERROR);
		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_SpecPath, getSpecPath());
	    return options;
	}

    /*package*/ static String getSpecPath() {
		String fileSeparator = File.separator; // under unix: '/'
		String pathSeparator = File.pathSeparator; // under unix: ':'
		// String user = System.getProperty("user.name");
		// String JML2_ROOT = System.getProperty("jml2.root");
		// String JML2specs = fileSeparator + "home" + fileSeparator + user + fileSeparator + "dev" + fileSeparator + "JML2" + fileSeparator + "specs";
		String sp = "." + pathSeparator 
			+ "." + fileSeparator + "specs" + pathSeparator
			+ "." + fileSeparator + "src" + pathSeparator;
			// + JML2specs;
		return sp;
    }

	public void test_0000_NullityKeywords() {
		this.runConformTest(
			new String[] {
				"NullityKeywords.java",
                "class NullityKeywords {\n" +
                "   /*@ non_null */ String non  = \"hello\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ String able = null;\n" +
                "   /*@ pure non_null */ String pnon  = \"hello\"; //$NON-NLS-1$\n" +
                "   /*@ pure nullable */ String pable = null;\n" +
                "}\n" });
	}
	public void test_0000a_NullityKeywords() {
		this.runNegativeTest(
			new String[] {
				"NullityKeywords.java",
                "class NullityKeywords {\n" +
                "   /*@ pure non_null */ String m1() { return null; }\n" +
                "   /*@ pure nullable */ String m2() { return null; }\n" +
                "   /*@ spec_public non_null */ String f1 = null;\n" +
                "   /*@ spec_protected non_null */ String f2 = null;\n" +
                "}\n"
			},
                "----------\n" +
                "1. ERROR in NullityKeywords.java (at line 2)\n" +
                "	/*@ pure non_null */ String m1() { return null; }\n" +
                "	                                   ^^^^^^^^^^^^\n" +
                "The method must return a non-null result\n" +
                "----------\n" +
                "2. ERROR in NullityKeywords.java (at line 4)\n" +
                "	/*@ spec_public non_null */ String f1 = null;\n" +
                "	                                   ^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "3. ERROR in NullityKeywords.java (at line 5)\n" +
                "	/*@ spec_protected non_null */ String f2 = null;\n" +
                "	                                      ^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n");
    }
    public void test_0001_AndExpression() {
		this.runNegativeTest(
			new String[] {
				"AndExpression.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "\n" +
                "class AndExpression {\n" +
                "   int m1(/*@ nullable */ String name, int x) { \n" +
                "      if (name!=null && name.length() > 0) \n" +
                "         return name.length(); \n" +
                "      else\n" +
                "         return x;\n" +
                "   }\n" +
                "   int m2(/*@ nullable */ String name, int x) { \n" +
                "      if (name!=null & name.length() > 0) \n" +
                "         return name.length(); \n" +
                "      else\n" +
                "         return x;\n" +
                "   }\n" +
                "   int m3(/*@ nullable */ String name, /*@ nullable */ String path, int x) { \n" +
                "      if (name!=null && path!=null) {\n" +
                "         if (name.length() > 0)\n" +
                "            return name.length();\n" +
                "         else\n" +
                "            return x;\n" +
                "      }\n" +
                "      else \n" +
                "         return 0;\n" +
                "   }\n" +
                "   int m4(/*@ nullable */ String name, /*@ nullable */ String path, int x) { \n" +
                "      if (path!=null && name!=null) {\n" +
                "         if (name.length() > 0)\n" +
                "            return name.length();\n" +
                "         else\n" +
                "            return x;\n" +
                "      }\n" +
                "      else \n" +
                "         return 0;\n" +
                "   }\n" +
                "   int m5(/*@ nullable */ String name, int x) { \n" +
                "      int y;\n" +
                "      if (name!=null && name.length() > 0) \n" +
                "         y=name.length(); \n" +
                "      else\n" +
                "         y=x;\n" +
                "      return y + name.length();\n" +
                "   }\n" +
                "   int m6(/*@ nullable */ String name, int x) { \n" +
                "      if (name!=null && name.length() > 0) \n" +
                "         return name.length(); \n" +
                "      else\n" +
                "         return name.length();\n" +
                "   }\n" +
                "   int m7(/*@ nullable */ String name, /*@ nullable */ String path, int x) { \n" +
                "      if (path!=null && name!=null) {\n" +
                "         if (path.length() > 0)\n" +
                "            return path.length();\n" +
                "         else\n" +
                "            return x;\n" +
                "      }\n" +
                "      else \n" +
                "         return 0;\n" +
                "   }\n" +
                "}\n"
			},
                "----------\n" +
                "1. ERROR in AndExpression.java (at line 14)\n" +
                "	if (name!=null & name.length() > 0) \n" +
                "	                 ^^^^\n" +
                "Potential null pointer access: The variable name may be null at this location\n" +
                "----------\n" +
                "2. ERROR in AndExpression.java (at line 45)\n" +
                "	return y + name.length();\n" +
                "	           ^^^^\n" +
                "Potential null pointer access: The variable name may be null at this location\n" +
                "----------\n" +
                "3. ERROR in AndExpression.java (at line 51)\n" +
                "	return name.length();\n" +
                "	       ^^^^\n" +
                "Potential null pointer access: The variable name may be null at this location\n" +
                "----------\n");
    }
    public void test_0002_ArrayExpression() {
		this.runNegativeTest(
			new String[] {
				"ArrayExpression.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class ArrayExpression {\n" +
                "   int i;\n" +
                "   /*@ non_null */ String[/*@non_null*/] non=new /*@non_null*/ String[]{\"hello\"}; //$NON-NLS-1$\n" +
                "   /*@ nullable */ String[] able;\n" +
                "\n" +
                "   int m1() { return this.non[i].length(); }\n" +
                "   int m2() { return this.non.length; }\n" +
                "   int m3() { return this.able.length; }   //error\n" +
                "   /*@ nullable */ String m3(int x) { return this.able[x]; } //error\n" +
                "\n" +
                "   /*@ nullable */ String[] f() { \n" +
                "     if (i==0) \n" +
                "        return null;\n" +
                "     else\n" +
                "        return new /*@ nullable */ String[] {\"hello\"}; //$NON-NLS-1$\n" +
                "   }\n" +
                "   /*@ nullable */ String m4(int x) { \n" +
                "     String[] names = f();\n" +
                "     if (names==null)\n" +
                "        return \"null\"; //$NON-NLS-1$\n" +
                "     else\n" +
                "        return names[x];\n" +
                "   }\n" +
                "   int m5(int x) {\n" +
                "     if (this.non!=null)\n" +
                "        return this.non.length;\n" +
                "     else\n" +
                "        return 0;\n" +
                "   }\n" +
                "   int m6(int x) {\n" +
                "     if (this.able!=null)\n" +
                "        return this.able.length; //error\n" +
                "     else\n" +
                "        return 0;\n" +
                "   }\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in ArrayExpression.java (at line 12)\n" +
                "	int m3() { return this.able.length; }   //error\n" +
                "	                  ^^^^^^^^^\n" +
                "Possible null dereference\n" +
                "----------\n" +
                "2. ERROR in ArrayExpression.java (at line 13)\n" +
                "	/*@ nullable */ String m3(int x) { return this.able[x]; } //error\n" +
                "	                                          ^^^^^^^^^\n" +
                "Possible null dereference\n" +
                "----------\n" +
                "3. ERROR in ArrayExpression.java (at line 36)\n" +
                "	return this.able.length; //error\n" +
                "	       ^^^^^^^^^\n" +
                "Possible null dereference\n" +
                "----------\n"
        );
    }
    public void test_0003_ArrayReference() {
		this.runNegativeTest(
			new String[] {
				"ArrayReference.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class ArrayReference {\n" +
                "	\n" +
                "	/*@ non_null */ Object[/*@non_null*/] non  = new Object[]{\"a\"}; //$NON-NLS-1$\n" +
                "	/*@ nullable */ Object[] able = new Object[]{\"a\"}; //$NON-NLS-1$\n" +
                "	/*@ non_null */ int[] iNon  = new int[]{1};\n" +
                "	/*@ nullable */ int[] iAble = new int[]{1};\n" +
                "   \n" +
                "   /*@ non_null */ Object m1() { return non[0]; }\n" +
                "   /*@ non_null */ Object m2() { return able[0]; }   // error\n" +
                "                      int m3() { return iNon[1]; }\n" +
                "                      int m4() { return iAble[1]; }  // error\n" +
                "}\n"
			},
                "----------\n" +
                "1. ERROR in ArrayReference.java (at line 13)\n" +
                "	/*@ non_null */ Object m2() { return able[0]; }   // error\n" +
                "	                              ^^^^^^^^^^^^^^^\n" +
                "The method must return a non-null result\n" +
                "----------\n" +
                "2. ERROR in ArrayReference.java (at line 13)\n" +
                "	/*@ non_null */ Object m2() { return able[0]; }   // error\n" +
                "	                                     ^^^^\n" +
                "Possible null dereference\n" +
                "----------\n" +
                "3. ERROR in ArrayReference.java (at line 15)\n" +
                "	int m4() { return iAble[1]; }  // error\n" +
                "	                  ^^^^^\n" +
                "Possible null dereference\n" +
                "----------\n"
        );
    }
    public void test_0004_AssignmentExpression() {
		this.runNegativeTest(
			new String[] {
				"AssignmentExpression.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class AssignmentExpression {\n" +
                "   /*@ non_null */ String non  = \"hello\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ String able = null;\n" +
                "\n" +
                "   void m1(/*@non_null*/ String s) { this.non = s; }\n" +
                "   void m2(/*@nullable*/ String s) { this.non = s; } //error\n" +
                "   void m3(/*@non_null*/ String s) { this.able = s; }\n" +
                "   void m4(/*@nullable*/ String s) { this.able = s; }\n" +
                "   void m7(/*@non_null*/ String s) { if (s!=null) this.non = s; }\n" +
                "   void m8(/*@nullable*/ String s) { if (s!=null) this.non = s; }\n" +
                "   void m9(/*@non_null*/ String s) { if (s!=null) this.able = s; }\n" +
                "   void m10(/*@nullable*/ String s) { if (s!=null) this.able = s; }\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in AssignmentExpression.java (at line 10)\n" +
                "	void m2(/*@nullable*/ String s) { this.non = s; } //error\n" +
                "	                                  ^^^^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "2. ERROR in AssignmentExpression.java (at line 13)\n" +
                "	void m7(/*@non_null*/ String s) { if (s!=null) this.non = s; }\n" +
                "	                                      ^\n" +
                "Redundant null check: The variable s cannot be null at this location\n" +
                "----------\n" +
                "3. ERROR in AssignmentExpression.java (at line 15)\n" +
                "	void m9(/*@non_null*/ String s) { if (s!=null) this.able = s; }\n" +
                "	                                      ^\n" +
                "Redundant null check: The variable s cannot be null at this location\n" +
                "----------\n" 
        );
    }
    public void test_0004a_AssignmentExpression() {
		this.runNegativeTest(
			new String[] {
				"AssignmentExpression.java",
                "class AssignmentExpression {\n" +
                "   /*@non_null*/ String non = \"\";\n" +
                "   /*@nullable*/ String able = non;\n" +
                "   static /*@non_null*/ String sNon = \"\";\n" +
                "   static /*@nullable*/ String sAble = sNon;\n" +
                "\n" +
                "   void m1() { non = null; }	// error\n" +
                "   void m2() { this.non = null; }	// error\n" +
                "   void m3() { able = null; }\n" +
                "   void m4() { this.able = null; }\n" +
                "\n" +
                "   void m1a(/*@nullable*/ String s) { non = s; }	// error\n" +
                "   void m2a(/*@nullable*/ String s) { this.non = s; }	// error\n" +
                "   void m3a(/*@nullable*/ String s) { able = s; }\n" +
                "   void m4a(/*@nullable*/ String s) { this.able = s; }\n" +
                "\n" +
                "   static void sm1() { sNon = null; }	// error\n" +
                "   static void sm3() { sAble = null; }\n" +
                "   static void sm1a(/*@nullable*/ String s) { sNon = s; }	// error\n" +
                "   static void sm3a(/*@nullable*/ String s) { sAble = s; }\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in AssignmentExpression.java (at line 7)\n" +
                "	void m1() { non = null; }	// error\n" + 
                "	            ^^^^^^^^^^\n" + 
                "Possible assignment of null to an L-value declared non_null\n" + 
                "----------\n" +
                "2. ERROR in AssignmentExpression.java (at line 8)\n" + 
                "	void m2() { this.non = null; }	// error\n" + 
                "	            ^^^^^^^^^^^^^^^\n" + 
                "Possible assignment of null to an L-value declared non_null\n" + 
                "----------\n" + 
                "3. ERROR in AssignmentExpression.java (at line 12)\n" + 
                "	void m1a(/*@nullable*/ String s) { non = s; }	// error\n" + 
                "	                                   ^^^^^^^\n" + 
                "Possible assignment of null to an L-value declared non_null\n" + 
                "----------\n" + 
                "4. ERROR in AssignmentExpression.java (at line 13)\n" + 
                "	void m2a(/*@nullable*/ String s) { this.non = s; }	// error\n" + 
                "	                                   ^^^^^^^^^^^^\n" + 
                "Possible assignment of null to an L-value declared non_null\n" + 
                "----------\n" + 
                "5. ERROR in AssignmentExpression.java (at line 17)\n" + 
                "	static void sm1() { sNon = null; }	// error\n" + 
                "	                    ^^^^^^^^^^^\n" + 
                "Possible assignment of null to an L-value declared non_null\n" + 
                "----------\n" + 
                "6. ERROR in AssignmentExpression.java (at line 19)\n" + 
                "	static void sm1a(/*@nullable*/ String s) { sNon = s; }	// error\n" + 
                "	                                           ^^^^^^^^\n" + 
                "Possible assignment of null to an L-value declared non_null\n" + 
                "----------\n" 
        );
    }
    public void test_0005_CastExpression() {
		this.runNegativeTest(
			new String[] {
				"CastExpression.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class CastExpression {\n" +
                "   \n" +
                "   int m1(/*@ nullable */ Object o) { return ((Object) o).hashCode(); }\n" +
                "   int m2(/*@ nullable */ Object o) { return ((/*@ non_null */ Object) o).hashCode(); }\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in CastExpression.java (at line 7)\n" +
                "	int m1(/*@ nullable */ Object o) { return ((Object) o).hashCode(); }\n" +
                "	                                          ^^^^^^^^^^^^\n" +
                "Potential null pointer access: The variable o may be null at this location\n" +
                "----------\n" 
        );
    }
    public void test_0006_CharArray() {
		this.runNegativeTest(
			new String[] {
				"CharArray.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "public class CharArray {\n" +
                "   /*@ non_null */ char[]  m1a( /*@ non_null */ char[] x1a) { return x1a; }\n" +
                "   /*@ nullable */ char[]  m1b( /*@ non_null */ char[] x1b) { return x1b; }\n" +
                "   /*@ non_null */ char[]  m2 ( /*@ nullable */ char[] x2)  { return x2; } // error\n" +
                "   \n" +
                "   boolean  m3a( /*@ non_null */ char[] xa) { return !(xa.length == 0);  }\n" +
                "   boolean  m3b( /*@ non_null */ char[] xb) { return  (xb.length == 0);  }\n" +
                "   boolean  m3c( /*@ non_null */ char[] xc) { return  (xc.length != 0);  }\n" +
                "\n" +
                "   int m4a() { char[] xa = m1a(new char[0]); return xa.length; }\n" +
                "   int m4b() { char[] xb = m1b(new char[0]); return xb.length; } // error\n" +
                "   int m5a() { return m1a(new char[0]).length; }\n" +
                "   int m5b() { return m1b(new char[0]).length; } // error\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in CharArray.java (at line 8)\n" +
                "	/*@ non_null */ char[]  m2 ( /*@ nullable */ char[] x2)  { return x2; } // error\n" +
                "	                                                           ^^^^^^^^^^\n" +
                "The method must return a non-null result\n" +
                "----------\n" +
                "2. ERROR in CharArray.java (at line 15)\n" +
                "	int m4b() { char[] xb = m1b(new char[0]); return xb.length; } // error\n" +
                "	                                                 ^^\n" +
                "Potential null pointer access: The variable xb may be null at this location\n" +
                "----------\n" +
                "3. ERROR in CharArray.java (at line 17)\n" +
                "	int m5b() { return m1b(new char[0]).length; } // error\n" +
                "	                   ^^^^^^^^^^^^^^^^\n" +
                "Possible null dereference\n" +
                "----------\n" 
        );
    }
    public void test_0006b_CharArray() {
		this.runNegativeTest(
			new String[] {
				"CharArray.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "public class CharArray {\n" +
                "   /*@ nullable */ char[]  m1b( /*@ non_null */ char[] x1b) { return x1b; }\n" +
                "   int m4b() { char[] xb = m1b(new char[0]); return xb.length; } // error\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in CharArray.java (at line 5)\n" +
                "	int m4b() { char[] xb = m1b(new char[0]); return xb.length; } // error\n" +
                "	                                                 ^^\n" +
                "Potential null pointer access: The variable xb may be null at this location\n" +
                "----------\n" 
        );
    }
    
    public void test_0007_ClassField() {
		this.runNegativeTest(
			new String[] {
				"ClassField.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class ClassField {\n" +
                "   /*@ nullable */ String able;\n" +
                "   /*@ non_null */ String non=\"name\"; //$NON-NLS-1$\n" +
                "\n" +
                "   static /*@ nullable */ String s_able;\n" +
                "   static /*@ non_null */ String s_non=\"name\"; //$NON-NLS-1$\n" +
                "\n" +
                "   int m1() { return able.length(); }   // error\n" +
                "   int m2() { return non.length();  }\n" +
                "   int m3() { return ClassField.s_able.length(); } // error\n" +
                "   int m4() { return ClassField.s_non.length();  }\n" +
                "   int m5() { return this.able.length(); } // error\n" +
                "   int m6() { return this.non.length();  }\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in ClassField.java (at line 12)\n" +
                "	int m1() { return able.length(); }   // error\n" +
                "	                  ^^^^\n" +
                "Possible null dereference\n" +
                "----------\n" +
                "2. ERROR in ClassField.java (at line 14)\n" +
                "	int m3() { return ClassField.s_able.length(); } // error\n" +
                "	                  ^^^^^^^^^^^^^^^^^\n" +
                "Possible null dereference\n" +
                "----------\n" +
                "3. ERROR in ClassField.java (at line 16)\n" +
                "	int m5() { return this.able.length(); } // error\n" +
                "	                  ^^^^^^^^^\n" +
                "Possible null dereference\n" +
                "----------\n" 
        );
    }
    public void test_0008_ConditionalExpression() {
		this.runNegativeTest(
			new String[] {
				"ConditionalExpression.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class ConditionalExpression {\n" +
                "   \n" +
                "   int m1(/*@ nullable */ Object o) { return (o==null ? o.hashCode() :  0); }\n" +
                "   int m2(/*@ nullable */ Object o) { return (o==null ? 0 :  o.hashCode()); }\n" +
                "   int m3(/*@ non_null */ CE_1 o) { return (o.hashCode() > 0 ? o.non : o.able).hashCode(); }\n" +
                "   int m4(/*@ non_null */ CE_1 o) { return (o.hashCode() > 0 ? o.non : o.non).hashCode(); }\n" +
				"	/*@non_null*/String m(/*@nullable*/String s) {\n" +
				"		return s == null ? \"\" : s;\n" +
				"	}\n" +
                "\n" +
                "}\n" +
                "\n" +
                "class CE_1 { \n" +
                "  /*@ non_null */ Object non = \"a\"; //$NON-NLS-1$\n" +
                "  /*@ nullable */ Object able;\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in ConditionalExpression.java (at line 7)\n" +
                "	int m1(/*@ nullable */ Object o) { return (o==null ? o.hashCode() :  0); }\n" +
                "	                                                     ^\n" +
                "Null pointer access: The variable o can only be null at this location\n" +
                "----------\n" +
                "2. ERROR in ConditionalExpression.java (at line 9)\n" +
                "	int m3(/*@ non_null */ CE_1 o) { return (o.hashCode() > 0 ? o.non : o.able).hashCode(); }\n" +
                "	                                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
                "Possible null dereference\n" +
                "----------\n" 
        );
    }
    
    public void test_0008_ConditionalExpression2() {
		this.runNegativeTest(
			new String[] {
				"ConditionalExpression2.java",
                "class ConditionalExpression2 {\n" +
                "	final static /*@non_null*/String ss1;\n" +
                "	final static /*@non_null*/String ss2;\n" +
                "	static {\n" +
                "		String ps = System.getProperty(\"abc\");\n" +
                "		ss1 = ps == null ? \"\" : ps;\n" +
                "		if(ps == null)\n" +
                "			ss2 = \"\";\n" +
                "		else\n" +
                "			ss2 = ps;\n" +
                "	}\n" +
                "}\n"
			},
			"" 
        );
    }
    public void test_0009_ConditionalOr() {
		this.runNegativeTest(
			new String[] {
				"ConditionalOr.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class ConditionalOr {\n" +
                "   \n" +
                "   void m(/*@ nullable */ Object o) {\n" +
                "      if (o==null || o.hashCode() > 0) { /*empty*/ }\n" +
                "   }\n" +
                "}\n" 
			},
			"");
    }
    public void test_0010_Dot() {
		this.runNegativeTest(
			new String[] {
				"Dot.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "public class Dot {\n" +
                "   /*@non_null*/ String non = \"name\"; //$NON-NLS-1$\n" +
                "   /*@nullable*/ String able;\n" +
                "\n" +
                "   /*@nullable*/ String  m1(/*@non_null*/ Dot x) { return x.non;  }\n" +
                "   /*@nullable*/ String  m2(/*@non_null*/ Dot x) { return x.able; }\n" +
                "   /*@nullable*/ String  m3(/*@nullable*/ Dot x) { return x.non;  } // error\n" +
                "   /*@nullable*/ String  m4(/*@nullable*/ Dot x) { return x.able; } // error\n" +
                "   /*@non_null*/ String  m5(/*@non_null*/ Dot x) { return x.non;  }\n" +
                "   /*@non_null*/ String  m6(/*@non_null*/ Dot x) { return x.able; } // error\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in Dot.java (at line 11)\n" +
                "	/*@nullable*/ String  m3(/*@nullable*/ Dot x) { return x.non;  } // error\n" +
                "	                                                       ^\n" +
                "Potential null pointer access: The variable x may be null at this location\n"+
                "----------\n" +
                "2. ERROR in Dot.java (at line 12)\n" +
                "	/*@nullable*/ String  m4(/*@nullable*/ Dot x) { return x.able; } // error\n" +
                "	                                                       ^\n" +
                "Potential null pointer access: The variable x may be null at this location\n"+
                "----------\n" +
                "3. ERROR in Dot.java (at line 14)\n" +
                "	/*@non_null*/ String  m6(/*@non_null*/ Dot x) { return x.able; } // error\n" +
                "	                                                ^^^^^^^^^^^^^^\n" +
                "The method must return a non-null result\n" +
                "----------\n" 
        );
    }
    public void test_0011_DoubleAssignment() {
		this.runNegativeTest(
			new String[] {
				"DoubleAssignment.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class DoubleAssignment {\n" +
                "   /*@ non_null */ String non_1=\"name\"; //$NON-NLS-1$\n" +
                "   /*@ non_null */ String non_2=\"path\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ String able_1;\n" +
                "   /*@ nullable */ String able_2;\n" +
                "\n" +
                "   void m1(/*@ nullable */ String s) { this.non_2  = this.non_1  = s; } // error\n" +
                "   void m2(/*@ nullable */ String s) { this.able_2 = this.non_1  = s; } // error\n" +
                "   void m3(/*@ nullable */ String s) { this.non_2  = this.able_1 = s; } // error\n" +
                "   void m4(/*@ nullable */ String s) { this.able_2 = this.able_1 = s; }\n" +
                "   void m5(/*@ non_null */ String s) { this.non_2  = this.non_1  = s; }\n" +
                "   void m6(/*@ non_null */ String s) { this.able_2 = this.non_1  = s; } \n" +
                "   void m7(/*@ non_null */ String s) { this.non_2  = this.able_1 = s; } // error\n" +
                "   void m8(/*@ non_null */ String s) { this.able_2 = this.able_1 = s; } \n" +
                "}\n" +
                "\n" +
                "\n" 
			},
                "----------\n" +
                "1. ERROR in DoubleAssignment.java (at line 11)\n" +
                "	void m1(/*@ nullable */ String s) { this.non_2  = this.non_1  = s; } // error\n" +
                "	                                                  ^^^^^^^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "2. ERROR in DoubleAssignment.java (at line 12)\n" +
                "	void m2(/*@ nullable */ String s) { this.able_2 = this.non_1  = s; } // error\n" +
                "	                                                  ^^^^^^^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "3. ERROR in DoubleAssignment.java (at line 13)\n" +
                "	void m3(/*@ nullable */ String s) { this.non_2  = this.able_1 = s; } // error\n" +
                "	                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "4. ERROR in DoubleAssignment.java (at line 17)\n" +
                "	void m7(/*@ non_null */ String s) { this.non_2  = this.able_1 = s; } // error\n" +
                "	                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n"
        );
    }
    public void test_0012_FieldInit() {
		this.runNegativeTest(
			new String[] {
				"FieldInit.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "public class FieldInit {\n" +
                "   final Object non   = \"hello\"; //$NON-NLS-1$\n" +
                "   final Object able  = null;\n" +
                "   final Object non_  = \"hello\"; //$NON-NLS-1$\n" +
                "   final Object able_ = null;\n" +
                "   \n" +
                "   /*@ non_null */ Object non1  = non;\n" +
                "   /*@ non_null */ Object non2  = able; // error\n" +
                "   /*@ nullable */ Object able1 = non;\n" +
                "   /*@ nullable */ Object able2 = able;\n" +
                " \n" +
                "   /*@ non_null */ Object non1_  = non_;\n" +
                "   /*@ non_null */ Object non2_  = able_; // error\n" +
                "   /*@ nullable */ Object able1_ = non_;\n" +
                "   /*@ nullable */ Object able2_ = able_;\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in FieldInit.java (at line 12)\n" +
                "	/*@ non_null */ Object non2  = able; // error\n" +
                "	                       ^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "2. ERROR in FieldInit.java (at line 17)\n" +
                "	/*@ non_null */ Object non2_  = able_; // error\n" +
                "	                       ^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" 
        );
    }
    public void test_0012b_FieldInit_this() {
		this.runNegativeTest(
			new String[] {
				"FieldInit.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "public class FieldInit {\n" +
                "   final Object non   = \"hello\"; //$NON-NLS-1$\n" +
                "   final Object able  = null;\n" +
                "   final Object non_  = \"hello\"; //$NON-NLS-1$\n" +
                "   final Object able_ = null;\n" +
                "   \n" +
                "   /*@ non_null */ Object non1  = this.non;\n" +
                "   /*@ non_null */ Object non2  = this.able; // error\n" +
                "   /*@ nullable */ Object able1 = this.non;\n" +
                "   /*@ nullable */ Object able2 = this.able;\n" +
                " \n" +
                "   /*@ non_null */ Object non1_  = this.non_;\n" +
                "   /*@ non_null */ Object non2_  = this.able_; // error\n" +
                "   /*@ nullable */ Object able1_ = this.non_;\n" +
                "   /*@ nullable */ Object able2_ = this.able_;\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in FieldInit.java (at line 12)\n" +
                "	/*@ non_null */ Object non2  = this.able; // error\n" +
                "	                       ^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "2. ERROR in FieldInit.java (at line 17)\n" +
                "	/*@ non_null */ Object non2_  = this.able_; // error\n" +
                "	                       ^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" 
        );
    }
    public void test_0013_FieldInOtherPackage() {
		this.runNegativeTest(
			new String[] {
				"FieldInOtherPackage.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "public class FieldInOtherPackage {\n" +
                "   /*@ non_null */ String  m1( /*@ non_null */ Dot_1 x) { return x.able; } //error\n" +
                "   /*@ non_null */ String  m2( /*@ non_null */ Dot_1 x) { return x.non;  }\n" +
                "}\n",
                "Dot_1.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "public class Dot_1 {\n" +
                "   /*@non_null*/ String non = \"name\"; //$NON-NLS-1$\n" +
                "   /*@nullable*/ String able;\n" +
                "}\n",
			},
                "----------\n" +
                "1. ERROR in FieldInOtherPackage.java (at line 6)\n" +
                "	/*@ non_null */ String  m1( /*@ non_null */ Dot_1 x) { return x.able; } //error\n" +
                "	                                                       ^^^^^^^^^^^^^^\n" +
                "The method must return a non-null result\n" +
                "----------\n" 
        );
    }
    public void test_0014_FlowAnalysis() {
		this.runNegativeTest(
			new String[] {
				"FlowAnalysis.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class FlowAnalysis1 {\n" +
                "   void m1(/*@ nullable */ String s) { /*empty*/ }\n" +
                "   void m2(/*@ non_null */ String s) { /*empty*/ }\n" +
                "   void m3(/*@ nullable */ String v, /*@ nullable */ String n) {\n" +
                "      if (n!=null) {\n" +
                "         m2(n);\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                "\n" +
                "class FlowAnalysis2 {\n" +
                "   void m1(/*@ nullable */ String s) { /*empty*/ }\n" +
                "   void m2(/*@ non_null */ String s) { /*empty*/ }\n" +
                "   void m3(/*@ nullable */ String v, /*@ nullable */ String n) {\n" +
                "      if (n!=null) {\n" +
                "         m2(n);\n" +
                "         n=v;\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                "\n" +
                "class FlowAnalysis3 {\n" +
                "   void m1(/*@ nullable */ String s) { /*empty*/ }\n" +
                "   void m2(/*@ non_null */ String s) { /*empty*/ }\n" +
                "   void m3(/*@ nullable */ String v, /*@ nullable */ String n) {\n" +
                "      if (n!=null) {\n" +
                "         m2(n);\n" +
                "         n=v;\n" +
                "         m2(n);\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                "\n" +
                "class FlowAnalysis4 {\n" +
                "   void m1(/*@ nullable */ String s) { /*empty*/ }\n" +
                "   void m2(/*@ non_null */ String s) { /*empty*/ }\n" +
                "   void m3(/*@ nullable */ String v, /*@ nullable */ String n) {\n" +
                "      if (n!=null) {\n" +
                "         if (n!=null) {\n" +
                "            m2(n);\n" +
                "            n=v;\n" +
                "         }\n" +
                "         m2(n);\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                "\n" +
                "class FlowAnalysis5 {\n" +
                "   void m1(/*@ nullable */ String s) { /*empty*/ }\n" +
                "   void m2(/*@ non_null */ String s) { /*empty*/ }\n" +
                "   void m3(/*@ nullable */ String v, /*@ nullable */ String n) {\n" +
                "      n=\"a\"; //$NON-NLS-1$\n" +
                "      n=v;\n" +
                "   }\n" +
                "}\n" +
                "\n" +
                "// from nice.sourceforge.net OptionTypes\n" +
                "class FlowAnalysis6\n" +
                "{\n" +
                "  /*@nullable*/ String name;\n" +
                "\n" +
                "   void process(/*@non_null*/FlowAnalysis6 a)\n" +
                "   {\n" +
                "       /*@nullable*/ String localName = a.name;\n" +
                "       if (localName != null) {\n" +
                "    	   int len = localName.length();\n" +
                "    	   if(len > 0) { /**/ }\n" +
                "       } else\n" +
                "       { /*empty*/ }\n" +
                "   }\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in FlowAnalysis.java (at line 33)\n" +
                "	m2(n);\n" +
                "	^^^^^\n" +
                "Possibly null actual parameter cannot be assigned to non_null formal parameter 1, s\n" +
                "----------\n" +
                "2. ERROR in FlowAnalysis.java (at line 43)\n" +
                "	if (n!=null) {\n" +
                "	    ^\n" +
                "Redundant null check: The variable n cannot be null at this location\n" +
                "----------\n" +
                "3. ERROR in FlowAnalysis.java (at line 47)\n" +
                "	m2(n);\n" +
                "	^^^^^\n" +
                "Possibly null actual parameter cannot be assigned to non_null formal parameter 1, s\n" +
                "----------\n" 
        );
    }
    public void test_0015_IfGuard() {
		this.runNegativeTest(
			new String[] {
				"IfGuard.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class IfGuard1 {\n" +
                "   int x;\n" +
                "   /*@nullable*/ String f() {\n" +
                "	   if (x==0) return null;\n" +
                "	   else      return \"hello\"; //$NON-NLS-1$\n" +
                "   }\n" +
                "   int m(int localX) { \n" +
                "   /*@nullable*/ String name=f();\n" +
                "      if (name!=null)\n" +
                "         return name.length();\n" +
                "      else\n" +
                "         return localX;\n" +
                "   }\n" +
                "}\n" +
                "\n" +
                "class IfGuard2 {\n" +
                "   /*@nullable*/ String f(int x) {\n" +
                "	   if (x==0) return null;\n" +
                "	   else      return \"hello\"; //$NON-NLS-1$\n" +
                "   }\n" +
                "   int m(int x) { \n" +
                "   /*@nullable*/ String name=f(x);\n" +
                "      if (name==null)\n" +
                "         return x;\n" +
                "      else\n" +
                "         return name.length();\n" +
                "   }\n" +
                "}\n" 
			},
			"");
    }
    public void test_0016_Instanceof() {
		this.runNegativeTest(
			new String[] {
				"Instanceof.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class Instanceof {\n" +
                "   void m(/*@ nullable */Object o) {\n" +
                "      if (o instanceof String) {\n" +
                "         o.hashCode();\n" +
                "      } \n" +
                "   }\n" +
                "}\n" 
			},
			"");
    }
    public void test_0017_LineComment() {
		this.runNegativeTest(
			new String[] {
				"LineComment.java",
                "\n" +
                "//@ nullable_by_default\n" +
                "\n" +
                "\n" +
                "\n" +
                "class LineComment {\n" +
                "   //@non_null\n" +
                "     String non = \"hello\"; //$NON-NLS-1$\n" +
                "   //@nullable\n" +
                "     String able;\n" +
                "\n" +
                "   //@nullable\n" +
                "     String m1() { return this.non; }\n" +
                "}\n" 
			},
			"");
    }
    public void test_0018_MethodCallHavoc() {
		this.runNegativeTest(
			new String[] {
				"MethodCallHavoc.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "//nullable fields are never to be trusted to be non-null, since another \n" +
                "//thread can set them to null...\n" +
                "class MethodCallHavoc1 {\n" +
                "\n" +
                "   public /*@nullable*/ String myString;\n" +
                "\n" +
                "   public void bar ()\n" +
                "   {\n" +
                "      myString = null;\n" +
                "   }\n" +
                "\n" +
                "   public void foo () {\n" +
                "      if (myString != null) {   // Okay, if we enter the block we know that myString is not null\n" +
                "         bar ();                           // This call may invalidate the nullness of myString\n" +
                "         myString = /*@(non_null String)*/(myString.trim()); // And at run-time, we find out it does!\n" +
                "      }\n" +
                "   }\n" +
                "}   \n" +
                "//success\n" +
                "//non-null fields are always to be trusted to be non-null, since there's\n" +
                "//no way for them to be non-null after a constructor finishes\n" +
                "class MethodCallHavoc2 {\n" +
                "\n" +
                "   public /*@non_null*/ String myString=\"hello\"; //$NON-NLS-1$\n" +
                "\n" +
                "   public void bar ()\n" +
                "   {\n" +
                "      myString = \"world\"; //$NON-NLS-1$\n" +
                "   }\n" +
                "\n" +
                "   public void foo () {\n" +
                "      if (myString != null) {\n" +
                "         bar ();\n" +
                "         myString = /*@(non_null String)*/(myString.trim());\n" +
                "      }\n" +
                "   }\n" +
                "}\n" +
                "//success\n" +
                "//nullable fields are never to be trusted to be non-null, since another \n" +
                "//thread can set them to null...\n" +
                "class MethodCallHavoc3 {\n" +
                "\n" +
                "   public /*@nullable*/ String myString;\n" +
                "\n" +
                "   public /*@non_null*/ String baz() {\n" +
                "	   return \"hello\"; //$NON-NLS-1$\n" +
                "   }\n" +
                "   public void bar ()\n" +
                "   {\n" +
                "      myString = null;\n" +
                "   }\n" +
                "\n" +
                "   public void foo () {\n" +
                "      String localString = baz();\n" +
                "      if (localString != null) {\n" +
                "         bar ();\n" +
                "         myString = localString.trim();\n" +
                "      }\n" +
                "   }\n" +
                "}   \n" 
			},
                "----------\n" +
                "1. ERROR in MethodCallHavoc.java (at line 18)\n" +
                "	myString = /*@(non_null String)*/(myString.trim()); // And at run-time, we find out it does!\n" +
                "	                                  ^^^^^^^^\n" +
                "Possible null dereference\n" +
                "----------\n" +
                "2. ERROR in MethodCallHavoc.java (at line 58)\n" +
                "	if (localString != null) {\n" +
                "	    ^^^^^^^^^^^\n" +
                "Redundant null check: The variable localString cannot be null at this location\n" +
                "----------\n" 
        );
    }
    public void test_0019_MethodCall() {
		this.runNegativeTest(
			new String[] {
				"MethodCall.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "public class MethodCall {\n" +
                "   /*@ non_null */ Object non  = \"a\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ Object able = \"a\"; //$NON-NLS-1$\n" +
                "   void non (/*@non_null*/ Object o) { /*empty*/ }\n" +
                "   void able(/*@nullable*/ Object o) { /*empty*/ }\n" +
                "   void m1() { non(non);  }\n" +
                "   void m2() { non(able); }  // error\n" +
                "   void m3() { able(non);  }\n" +
                "   void m4() { able(able); }\n" +
                "\n" +
                "   void m5() {   non(\"a\"); } //$NON-NLS-1$\n" +
                "   void m6(/*@ non_null */ String s) { s.length(); }\n" +
                "   void m7(/*@ nullable */ String s) { s.length(); }  // error\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in MethodCall.java (at line 11)\n" +
                "	void m2() { non(able); }  // error\n" +
                "	            ^^^^^^^^^\n" +
                "Possibly null actual parameter cannot be assigned to non_null formal parameter 1, o\n" +
                "----------\n" +
                "2. ERROR in MethodCall.java (at line 17)\n" +
                "	void m7(/*@ nullable */ String s) { s.length(); }  // error\n" +
                "	                                    ^\n" +
                "Potential null pointer access: The variable s may be null at this location\n" +
                "----------\n" 
        );
    }
    public void test_0020_MethodCall_target() {
		this.runNegativeTest(
			new String[] {
				"MethodCall_target.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class MethodCall_target {\n" +
                "   /*@ non_null */ Object non  = \"a\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ Object able = \"a\"; //$NON-NLS-1$\n" +
                "   void non (/*@non_null*/ Object o){ /*empty*/ }\n" +
                "   void able(/*@nullable*/ Object o){ /*empty*/ }\n" +
                "}\n" 
			},
			"");
    }
    public void test_0021_MethodCallThenField() {
		this.runNegativeTest(
			new String[] {
				"MethodCallThenField.java",
                "\n" +
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "public class MethodCallThenField {\n" +
                "   \n" +
                "   int field = 0;\n" +
                "   /*@non_null*/ MethodCallThenField f_non = this;\n" +
                "   /*@nullable*/ MethodCallThenField f_able;\n" +
                "   /*@non_null*/ MethodCallThenField non() { return this; }\n" +
                "   /*@nullable*/ MethodCallThenField able() { return null; }\n" +
                "\n" +
                "   int m1() { return this.non().field; }\n" +
                "   int m2() { return this.able().field; } // error\n" +
                "\n" +
                "   int m3(/*@ non_null */ MethodCallThenField p) { return p.non().field; }\n" +
                "   int m4(/*@ non_null */ MethodCallThenField p) { return p.able().field; } // error\n" +
                "\n" +
                "   int m5(/*@ non_null */ MethodCallThenField p) { return p.non().non().field; }\n" +
                "   int m6(/*@ non_null */ MethodCallThenField p) { return p.non().able().field; } // error\n" +
                "   int m7(/*@ non_null */ MethodCallThenField p) { return p.able().non().field; } // error\n" +
                "   int m8(/*@ non_null */ MethodCallThenField p) { return p.able().able().field; } // error\n" +
                "\n" +
                "   int f_m1() { return f_non.non().non().field; }\n" +
                "   int f_m2() { return f_non.non().able().field; } // error\n" +
                "   int f_m3() { return f_non.able().non().field; } // error\n" +
                "   int f_m4() { return f_non.able().able().field; } // error\n" +
                "   int f_m5() { return f_able.non().non().field; } // error\n" +
                "   int f_m6() { return f_able.non().able().field; } // error\n" +
                "   int f_m7() { return f_able.able().non().field; } // error\n" +
                "   int f_m8() { return f_able.able().able().field; } // error\n" +
                "}\n"
			},
	          "----------\n"+
	          "1. ERROR in MethodCallThenField.java (at line 15)\n" +
	          "	int m2() { return this.able().field; } // error\n" +
	          "	                  ^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "2. ERROR in MethodCallThenField.java (at line 18)\n" +
	          "	int m4(/*@ non_null */ MethodCallThenField p) { return p.able().field; } // error\n" +
	          "	                                                       ^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "3. ERROR in MethodCallThenField.java (at line 21)\n" +
	          "	int m6(/*@ non_null */ MethodCallThenField p) { return p.non().able().field; } // error\n" +
	          "	                                                       ^^^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "4. ERROR in MethodCallThenField.java (at line 22)\n" +
	          "	int m7(/*@ non_null */ MethodCallThenField p) { return p.able().non().field; } // error\n" +
	          "	                                                       ^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "5. ERROR in MethodCallThenField.java (at line 23)\n" +
	          "	int m8(/*@ non_null */ MethodCallThenField p) { return p.able().able().field; } // error\n" +
	          "	                                                       ^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "6. ERROR in MethodCallThenField.java (at line 23)\n" +
	          "	int m8(/*@ non_null */ MethodCallThenField p) { return p.able().able().field; } // error\n" +
	          "	                                                       ^^^^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "7. ERROR in MethodCallThenField.java (at line 26)\n" +
	          "	int f_m2() { return f_non.non().able().field; } // error\n" +
	          "	                    ^^^^^^^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "8. ERROR in MethodCallThenField.java (at line 27)\n" +
	          "	int f_m3() { return f_non.able().non().field; } // error\n" +
	          "	                    ^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "9. ERROR in MethodCallThenField.java (at line 28)\n" +
	          "	int f_m4() { return f_non.able().able().field; } // error\n" +
	          "	                    ^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "10. ERROR in MethodCallThenField.java (at line 28)\n" +
	          "	int f_m4() { return f_non.able().able().field; } // error\n" +
	          "	                    ^^^^^^^^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "11. ERROR in MethodCallThenField.java (at line 29)\n" +
	          "	int f_m5() { return f_able.non().non().field; } // error\n" +
	          "	                    ^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "12. ERROR in MethodCallThenField.java (at line 30)\n" +
	          "	int f_m6() { return f_able.non().able().field; } // error\n" +
	          "	                    ^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "13. ERROR in MethodCallThenField.java (at line 30)\n" +
	          "	int f_m6() { return f_able.non().able().field; } // error\n" +
	          "	                    ^^^^^^^^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "14. ERROR in MethodCallThenField.java (at line 31)\n" +
	          "	int f_m7() { return f_able.able().non().field; } // error\n" +
	          "	                    ^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "15. ERROR in MethodCallThenField.java (at line 31)\n" +
	          "	int f_m7() { return f_able.able().non().field; } // error\n" +
	          "	                    ^^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "16. ERROR in MethodCallThenField.java (at line 32)\n" +
	          "	int f_m8() { return f_able.able().able().field; } // error\n" +
	          "	                    ^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "17. ERROR in MethodCallThenField.java (at line 32)\n" +
	          "	int f_m8() { return f_able.able().able().field; } // error\n" +
	          "	                    ^^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n" +
	          "18. ERROR in MethodCallThenField.java (at line 32)\n" +
	          "	int f_m8() { return f_able.able().able().field; } // error\n" +
	          "	                    ^^^^^^^^^^^^^^^^^^^^\n" +
	          "Possible null dereference\n" +
	          "----------\n");
    }
    public void test_0022_MethodInOtherPackage_Call() {
		this.runNegativeTest(
			new String[] {
				"MethodInOtherPackage_Call.java",
                "/*@ nullable_by_default */\n" +
                "class MethodInOtherPackage_Call {\n" +
                "   final /*@ non_null */ MethodCall_target target = \n" +
                "	             new MethodCall_target();\n" +
                "   /*@ non_null */ Object non  = \"a\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ Object able = \"a\"; //$NON-NLS-1$\n" +
                "   void m1() { target.non(non);  }\n" +
                "   void m2() { target.non(able); }  // error\n" +
                "   void m3() { target.able(non);  }\n" +
                "   void m4() { target.able(able); }\n" +
                "   void m5() { target.non(\"a\"); } //$NON-NLS-1$\n" +
                "   void m6() { MethodCall_target.static_non(able); } // error\n" +
                "}\n",
                "MethodCall_target.java",
                "/*@ nullable_by_default */\n" +
                "class MethodCall_target {\n" +
                "   /*@ non_null */ Object non  = \"a\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ Object able = \"a\"; //$NON-NLS-1$\n" +
                "   void non (/*@non_null*/ Object o){ /*empty*/ }\n" +
                "   void able(/*@nullable*/ Object o){ /*empty*/ }\n" +
                "   static void static_non (/*@non_null*/ Object o){ /*empty*/ }\n" +
                "}\n"
			},
                "----------\n" +
                "1. ERROR in MethodInOtherPackage_Call.java (at line 8)\n" +
                "	void m2() { target.non(able); }  // error\n" +
                "	            ^^^^^^^^^^^^^^^^\n" +
                "Possibly null actual parameter cannot be assigned to non_null formal parameter 1, o\n" +
                "----------\n" +
                "2. ERROR in MethodInOtherPackage_Call.java (at line 12)\n" +
                "	void m6() { MethodCall_target.static_non(able); } // error\n" +
                "	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
                "Possibly null actual parameter cannot be assigned to non_null formal parameter 1, o\n" +
                "----------\n" 
        );
    }
    public void test_0023_NeedHelpFromSpec() {
    	
		this.runNegativeTest(
			new String[] {
				"NeedHelpFromSpec.java",
                "\n" +
                "\n" +
                "public class NeedHelpFromSpec {\n" +
                "   Object non  = \"a\"; //$NON-NLS-1$\n" +
                "   Object able = \"a\"; //$NON-NLS-1$\n" +
                "   void non (Object o) { /*empty*/ }\n" +
                "   void able(Object o) { /*empty*/ }\n" +
                "   void m1() { non(non);  }\n" +
                "   void m2() { non(able); }  // error\n" +
                "   void m3() { able(non);  }\n" +
                "   void m4() { able(able); }\n" +
                "\n" +
                "   void m5() {   non(\"a\"); } //$NON-NLS-1$\n" +
                "   void m6(String s) { s.length(); }\n" +
                "   void m7(String s) { s.length(); }  // error\n" +
                "}\n",
			},
                "----------\n" +
                "1. ERROR in NeedHelpFromSpec.java (at line 9)\n" +
                "	void m2() { non(able); }  // error\n" +
                "	            ^^^^^^^^^\n" +
                "Possibly null actual parameter cannot be assigned to non_null formal parameter 1, o\n" +
                "----------\n" +
                "2. ERROR in NeedHelpFromSpec.java (at line 15)\n" +
                "	void m7(String s) { s.length(); }  // error\n" +
                "	                    ^\n" +
                "Potential null pointer access: The variable s may be null at this location\n" +
                "----------\n"
        );
    }
	public void test_0024_multipleModifiers() {
		this.runNegativeTest(
			new String[] {
				"NullityKeywords.java",
                "class NullityKeywords {\n" +
                "   /*@ non_null */ /*@ non_null */ String n_n  = \"hello\"; //$NON-NLS-1$\n" +
                "   /*@ non_null */ /*@ nullable */ String n_a  = \"hello\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ /*@ non_null */ String a_n  = \"hello\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ /*@ nullable */ String a_a  = \"hello\"; //$NON-NLS-1$\n" +
                "}\n" },
                "----------\n" +
                "1. ERROR in NullityKeywords.java (at line 2)\n" +
                "	/*@ non_null */ /*@ non_null */ String n_n  = \"hello\"; //$NON-NLS-1$\n" +
                "	                    ^^^^^^^^\n" +
                "Syntax error on token \"non_null\", delete this token\n" +
                "----------\n" +
                "2. ERROR in NullityKeywords.java (at line 3)\n" +
                "	/*@ non_null */ /*@ nullable */ String n_a  = \"hello\"; //$NON-NLS-1$\n" +
                "	                    ^^^^^^^^\n" +
                "Syntax error on token \"nullable\", delete this token\n" +
                "----------\n" +
                "3. ERROR in NullityKeywords.java (at line 4)\n" +
                "	/*@ nullable */ /*@ non_null */ String a_n  = \"hello\"; //$NON-NLS-1$\n" +
                "	                    ^^^^^^^^\n" +
                "Syntax error on token \"non_null\", delete this token\n" +
                "----------\n" +
                "4. ERROR in NullityKeywords.java (at line 5)\n" +
                "	/*@ nullable */ /*@ nullable */ String a_a  = \"hello\"; //$NON-NLS-1$\n" +
                "	                    ^^^^^^^^\n" +
                "Syntax error on token \"nullable\", delete this token\n" +
                "----------\n");
	}
    public void test_0037_NullLiteral() {
		this.runNegativeTest(
			new String[] {
				"NullLiteral.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class NullLiteral {\n" +
                "   /*@non_null*/ String non=\"hello\"; //$NON-NLS-1$\n" +
                "   /*@nullable*/ String able;\n" +
                "\n" +
                "   void m1() { this.non  = null; }                //error\n" +
                "   void m2() { this.able = null; }\n" +
                "   /*@non_null*/ String m3() { return null; }     //error\n" +
                "   /*@nullable*/ String m4() { return null; }\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in NullLiteral.java (at line 9)\n" +
                "	void m1() { this.non  = null; }                //error\n" +
                "	            ^^^^^^^^^^^^^^^^\n" +
                "Possible assignment of null to an L-value declared non_null\n" +
                "----------\n" +
                "2. ERROR in NullLiteral.java (at line 11)\n" +
                "	/*@non_null*/ String m3() { return null; }     //error\n" +
                "	                            ^^^^^^^^^^^^\n" +
                "The method must return a non-null result\n" +
                "----------\n"
        );
    }
    public void test_0038_Nully() {
		this.runNegativeTest(
			new String[] {
				"Nully.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "//these cases were inspired by paper on Nully\n" +
                "class Nully {\n" +
                "   /*@non_null*/ String m1() { return \"\";   } //$NON-NLS-1$\n" +
                "   /*@non_null*/ String m3() { return System.getProperty(\"property\"); } //$NON-NLS-1$\n" +
                "   /*@nullable*/ String m4() { return System.getProperty(\"property\"); } //$NON-NLS-1$\n" +
                "\n" +
                "   void m5(/*@nullable*/ String s) {\n" +
                "          /*@nullable*/ String t=s;\n" +
                "          if (t!=null) \n" +
                "             p1(s);\n" +
                "   }\n" +
                "   void p1(/*@non_null */String s) { /*empty*/ }\n" +
                "\n" +
                "   void m6(/*@nullable */ String s) {\n" +
                "          /*@ nullable */ String t=s;\n" +
                "          p2(s);\n" +
                "   }\n" +
                "   void p2(/*@nullable */ String s) { /*empty*/ }\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in Nully.java (at line 8)\n" +
                "	/*@non_null*/ String m3() { return System.getProperty(\"property\"); } //$NON-NLS-1$\n" +
                "	                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
                "The method must return a non-null result\n" +
                "----------\n" +
                "2. ERROR in Nully.java (at line 14)\n" +
                "	p1(s);\n" +
                "	^^^^^\n" +
                "Possibly null actual parameter cannot be assigned to non_null formal parameter 1, s\n" +
                "----------\n");
    }
    public void test_0039_Return() {
		this.runNegativeTest(
			new String[] {
				"Return.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class Return {\n" +
                "   /*@non_null*/ String non = \"hello\"; //$NON-NLS-1$\n" +
                "   /*@nullable*/ String able;\n" +
                "\n" +
                "   /*@nullable*/ String m1() { return this.non; }\n" +
                "   /*@non_null*/ String m2() { return this.non; }\n" +
                "   /*@nullable*/ String m3() { return this.able; }\n" +
                "   /*@non_null*/ String m4() { return this.able; }\n" +
                "}\n" 
			},
                "----------\n" +
                "1. ERROR in Return.java (at line 12)\n" +
                "	/*@non_null*/ String m4() { return this.able; }\n" +
                "	                            ^^^^^^^^^^^^^^^^^\n" +
                "The method must return a non-null result\n" +
                "----------\n" 
        );
    }
	public void test_0039a_Return() {
		this.runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"	public static /*@non_null*/ X m() {\n" +
					"		X x = new X();\n" +
					"		return x;\n" +
					"	}\n" +
					"	public static /*@non_null*/ X[] ma() {\n" +
					"		X[] xa = new X[0];\n" +
					"		return xa;\n" +
					"	}\n" +
					"	public static /*@non_null*/ X m2() {\n" +
					"		X x = null;\n" +
					"		return (x = new X());\n" +
					"	}\n" +
	                "}\n"},
	        		"");
	}
    public void test_0042_Spec() {
		this.runNegativeTest(
			new String[] {
				"Spec.java",
                "// success\n" +
                "\n" +
                "\n" +
                "\n" +
                "public class Spec {\n" +
                "   public int x;\n" +
                "   public /*@pure*/ int f() { return 10; }\n" +
                "\n" +
                "   //@ requires a[0] > 0;\n" +
                "   public void m1(/*@non_null@*/ int[] a) { /*empty*/ }\n" +
                "   //@ requires a[0] > 0;\n" +
                "   public void m2(/*@nullable@*/ int[] a) { /*empty*/ }\n" +
                "   //@ requires a.length > 0;\n" +
                "   public void m3(/*@non_null@*/ int[] a) { /*empty*/ }\n" +
                "   //@ requires a.length > 0;\n" +
                "   public void m4(/*@nullable@*/ int[] a) { /*empty*/ }\n" +
                " \n" +
                "   //@ requires a.x > 0;\n" +
                "   public void m5(/*@non_null@*/ Spec a) { /*empty*/ }\n" +
                "   //@ requires a.x > 0;\n" +
                "   public void m6(/*@nullable@*/ Spec a) { /*empty*/ }\n" +
                "\n" +
                "   //@ requires a.f() > 0;\n" +
                "   public void m7(/*@non_null@*/ Spec a) { /*empty*/ }\n" +
                "   //@ requires a.f() > 0;\n" +
                "   public void m8(/*@nullable*/ Spec a) { /*empty*/ }\n" +
                "}\n" 
			},
			"");
    }
    public void test_0043_This() {
		this.runNegativeTest(
			new String[] {
				"This.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class This {\n" +
                "   static /*@ non_null */ Object s_non = \"a\"; //$NON-NLS-1$\n" +
                "   static /*@ nullable */ Object s_able;\n" +
                "   /*@ non_null */ Object non = \"a\"; //$NON-NLS-1$\n" +
                "   /*@ nullable */ Object able;\n" +
                "   \n" +
                "   /*@ nullable */ Object m1() { return this.non; }\n" +
                "   /*@ nullable */ Object m2() { return this.able; }\n" +
                "   /*@ nullable */ Object m3() { return This.s_non; }\n" +
                "   /*@ nullable */ Object m4() { return This.s_able; }\n" +
                "\n" +
                "}\n" 
			},
			"");
    }
    public void test_0044_Tilde() {
		this.runNegativeTest(
			new String[] {
				"Tilde.java",
                "/*@ nullable_by_default */\n" +
                "\n" +
                "\n" +
                "\n" +
                "class Tilde {\n" +
                "          int i;\n" +
                "   static int s_i;\n" +
                "          boolean b;\n" +
                "   static boolean s_b;\n" +
                "\n" +
                "   public int     m_int()  {return i;}\n" +
                "   public boolean m_bool() {return b;}\n" +
                "   \n" +
                "   int m1() { return this.i; }\n" +
                "   int m2() { return ~this.i; }\n" +
                "   int m3() { return Tilde.s_i; }\n" +
                "   int m4() { return ~Tilde.s_i; }\n" +
                "   int m5() { return i; }\n" +
                "   int m6() { return ~i; }\n" +
                "   int m7() { return this.m_int(); }\n" +
                "   int m8() { return ~this.m_int(); }\n" +
                " \n" +
                "   boolean m1_1() { return this.b; }\n" +
                "   boolean m2_1() { return !this.b; }\n" +
                "   boolean m3_1() { return Tilde.s_b; }\n" +
                "   boolean m4_1() { return !Tilde.s_b; }\n" +
                "   boolean m5_1() { return b; }\n" +
                "   boolean m6_1() { return !b; }\n" +
                "   boolean m7_1() { return this.m_bool(); }\n" +
                "   boolean m8_1() { return !this.m_bool(); }\n" +
                "}\n" 
			},
			"");
    }

    public void test_0047_Assignment_Primitive() {
		this.runNegativeTest(
				new String[] {
					"AssignmentTest.java",
	                "public class AssignmentTest {\n" +
	                "   public static void main(/*@nullable*/ String [] args) {\n" +
	                "      int i = args.length;\n" +
	                "   }\n" +
	                "}\n" },
	                "----------\n" +
	                "1. ERROR in AssignmentTest.java (at line 3)\n" +
	                "	int i = args.length;\n" +
	                "	        ^^^^\n" +
	                "Potential null pointer access: The variable args may be null at this location\n" +
	                "----------\n");
    }
    public void test_0048_Assignment_Primitive() {
		this.runConformTest(
				new String[] {
					"AssignmentTest.java",
	                "public class AssignmentTest {\n" +
	                "   public static void main(/*@non_null*/ String [] args) {\n" +
	                "      int i = args.length;\n" +
	                "   }\n" +
	                "}\n" });
    }
    public void test_0049_Initialize_primitive() {
		this.runConformTest(
				new String[] {
					"PrimInitTest.java",
	                "public class PrimInitTest {\n" +
	                "    private static final int sfX = Integer.MAX_VALUE;\n" + 
	                "    private static final int sfY = sfX;\n" + 
	                "    private static int sX = Integer.MAX_VALUE;\n" + 
	                "    private static int sY = sX;\n" + 
	                "    private final int fX = Integer.MAX_VALUE;\n" + 
	                "    private final int fY = fX;\n" + 
	                "    private int X = Integer.MAX_VALUE;\n" + 
	                "    private int Y = X;\n" + 
	                "}\n" });
    }
    public void test_0050_Initialization() {
		this.runConformTest(
				new String[] {
					"NNTest1.java",
	                "public class NNTest1 {\n" +
	                " 	private /*@ non_null */String s1;\n" +
	                " 	private /*@ non_null */String s2;\n" +
	                "	public NNTest1() {	// (*)\n" +
	                "		this.s1 = \"\";\n" +
	                "		s2 = \"\";\n" +
	                "	}\n" +
	                "}\n"});
    }
      
	public void test_0025_nn_field_init_1() {
		this.runConformTest(
			new String[] {
				"nn_field_init_1.java",
	            "\n" +
	            "\n" +
	            "public class nn_field_init_1 {\n" +
	            "\n" +
	            "	/*@ non_null */ nn_field_init_1 non  = this;\n" +
	            "	/*@ nullable */ nn_field_init_1 able = null;\n" +
	            "\n" +
	            "}\n" 
			},
			"");
	}

	public void test_0026_nn_field_init_2() {
		this.runNegativeTest(
			new String[] {
				"nn_field_init_2.java",
	            "\n" +
	            "\n" +
	            "public class nn_field_init_2 {\n" +
	            "\n" +
	            "	/*@ non_null */ nn_field_init_2 non  = null;\n" +
	            "}\n" 
			},
			"----------\n"+
			"1. ERROR in nn_field_init_2.java (at line 5)\n"+
			"	/*@ non_null */ nn_field_init_2 non  = null;\n"+
			"	                                ^^^\n"+
			"Possible assignment of null to an L-value declared non_null\n"+
			"----------\n");
	}

	public void test_0027_nn_field_init_3() {
		this.runNegativeTest(
			new String[] {
				"nn_field_init_3.java",
	            "\n" +
	            "\n" +
	            "public class nn_field_init_3 {\n" +
	            "\n" +
	            "	static /*@ non_null */ Object non  = \"\"; //$NON-NLS-1$\n" +
	            "	static /*@ nullable */ Object able = null;\n" +
	            "\n" +
	            "}\n" 
			},
			"");
	}

	public void test_0028_nn_field_init_4() {
		this.runNegativeTest(
			new String[] {
				"nn_field_init_4.java",
	            "\n" +
	            "\n" +
	            "public class nn_field_init_4 {\n" +
	            "\n" +
	            "	static /*@ non_null */ nn_field_init_4 non  = null;\n" +
	            "\n" +
	            "}\n"
			},
			"----------\n" +
            "1. ERROR in nn_field_init_4.java (at line 5)\n" +
            "	static /*@ non_null */ nn_field_init_4 non  = null;\n" +
            "	                                       ^^^\n" +
            "Possible assignment of null to an L-value declared non_null\n" +
            "----------\n");
	}

	public void test_0029_nn_field_init_5() {
		this.runNegativeTest(
			new String[] {
				"nn_field_init_5.java",
	            "\n" +
	            "\n" +
	            "public class nn_field_init_5 {\n" +
	            "\n" +
	            "	/*@ non_null */ nn_field_init_5 non;\n" +
	            "\n" +
	            "}\n" 
			},
			"----------\n" +
			"1. ERROR in nn_field_init_5.java (at line 5)\n" +
			"	/*@ non_null */ nn_field_init_5 non;\n" +
			"	                                ^^^\n" +
			"non_null field non may not have been explicitly initialized\n" +
			"----------\n");
	}

	public void test_0030_nn_field_init_6() {
		this.runNegativeTest(
			new String[] {
				"nn_field_init_6.java",
	            "\n" +
	            "\n" +
	            "public class nn_field_init_6 {\n" +
	            "\n" +
	            "	static /*@ non_null */ nn_field_init_6 non;\n" +
	            "\n" +
	            "}\n" 
			},
			"----------\n" +
			"1. ERROR in nn_field_init_6.java (at line 5)\n" +
			"	static /*@ non_null */ nn_field_init_6 non;\n" +
			"	                                       ^^^\n" +
			"non_null field non may not have been explicitly initialized\n" +
			"----------\n");
	}

	public void test_0031_nn_field_init() {
		this.runNegativeTest(
			new String[] {
				"nn_field_init.java",
	            "public class nn_field_init {\n" +
	            "	/*@nullable*/ nn_field_init able;\n" +
	            "	int n;\n" +
	            "	void m() {\n" +
	            "		if(able == null || able.n == 0)\n" +
	            "			return;\n" +
	            "	}\n" +
	            "}\n" 
			},
			"----------\n" +
			"1. ERROR in nn_field_init.java (at line 5)\n" +
			"	if(able == null || able.n == 0)\n" +
			"	                   ^^^^^^\n" +
			"Possible null dereference at access of field n\n" +
			"----------\n");
	}

	public void test_0100_nn_while() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
	            "	void f() {\n" +
	            "       Object o = this;\n"+
	            "       while (o != null) {\n" +
	            "             o.toString();\n" +
	            "             o = null;\n" +
	            "       }\n" +
	            "       o.toString();\n" +
	            "   }\n" +
	            "}\n" 
			},
			"----------\n" +
			"1. ERROR in X.java (at line 8)\n" +
			"	o.toString();\n" +
			"	^\n" +
			"Null pointer access: The variable o can only be null at this location\n" +
			"----------\n");
	}
	public void test_0101_nn_for() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
	            "	void f() {\n" +
	            "       Object o = this;\n"+
	            "       for (int i=0; o != null; i++) {\n" +
	            "             o.toString();\n" +
	            "             o = null;\n" +
	            "       }\n" +
	            "       o.toString();\n" +
	            "   }\n" +
	            "}\n" 
			},
			"----------\n" +
			"1. ERROR in X.java (at line 8)\n" +
			"	o.toString();\n" +
			"	^\n" +
			"Null pointer access: The variable o can only be null at this location\n" +
			"----------\n");
	}
	public void test_0102_nn_while() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
	            "   public X(/*@non_null*/ String s) {}\n"+
	            "	public void m1(/*@non_null*/ String s) {\n" +
	            "	}\n" +
	            "	public void f() {\n" +
	            "		String s = \"\";\n" +
	            "		new X(s);\n" +
	            "		m1(s);\n" +
	            "		while (true) {\n" +
	            "			new X(s);\n" +
	            "			m1(s);\n" +
	            "		}\n" +
	            "	}\n" +
	            "}\n" 
			},
			"");
	}
	public void test_0103_nn_for() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
	            "   public X(/*@non_null*/ String s) {}\n"+
	            "	public void m1(/*@non_null*/ String s) {\n" +
	            "	}\n" +
	            "	public void f() {\n" +
	            "		String s = \"\";\n" +
	            "		new X(s);\n" +
	            "		m1(s);\n" +
	            "		for (int i = 0; i < 9; i++) {\n" +
	            "			new X(s);\n" +
	            "			m1(s);\n" +
	            "		}\n" +
	            "	}\n" +
	            "}\n" 
			},
			"");
	}
	public void test_0104_nn_for() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
	            "	public void m1(/*@non_null*/ String s) {\n" +
	            "	}\n" +
	            "	public void f() {\n" +
	            "		String s = \"\";\n" +
	            "		m1(s);\n" +
	            "		for (int i = 0; i < 9; i++) {\n" +
	            "			s.toString();\n" +
	            "		}\n" +
	            "	}\n" +
	            "}\n" 
			},
			"");
	}
	public void test_0105_basedOn_NullReferenceTest_test0449_while_nested() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"class X {\n" + 
				"  void foo(/*@nullable*/ Object p, boolean b) {\n" + 
				"    Object o = new Object();\n" + 
				"    while (b) {\n" + 
				"      while (b) {\n" + 
				"        o = p;\n" + // now o is unknown
				"      }\n" + 
				"    }\n" + 
				"    if (o != null) { /* */ }\n" + 
				"  }\n" + 
				"}"},
			"");
	} 
	public void test_0106_localAccess_fieldAccess_onReturn() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"class X {\n" + 
				"  /*@nullable*/ X fa;\n"+
				"  /*@non_null*/ X fn = new X();\n"+				
				"   X foo(/*@non_null*/X ln, /*@nullable*/X la, int i) {\n" +
				"	switch (i) {\n" + 
				"        case 1: return(ln);\n" +			//0
				"        case 2: return(ln.fa);\n" +		//0
				"        case 3: return(ln.fn);\n" +		//0
				"        case 4: return(ln.fa.fa);\n" + 	//1
				"        case 5: return(ln.fa.fn);\n" + 	//1
				"        case 6: return(ln.fn.fa);\n" +		//0
				"        case 7: return(ln.fn.fn);\n" +		//0
				"        case 8: return(ln.fa.fa.fa);\n" +	//2
				"        case 9: return(ln.fa.fa.fn);\n" +	//2				
				"        case 10:return(ln.fa.fn.fa);\n" +  //1
				"        case 11:return(ln.fa.fn.fn);\n" +	//1			
				"        case 12:return(ln.fn.fa.fa);\n" +	//1
				"        case 13:return(ln.fn.fa.fn);\n" +	//1				
				"        case 14:return(ln.fn.fn.fa = null);\n" +	//0
				"        case 15:return(ln.fn.fn.fn = null);\n" +	//1
				"        case 21:return(la);\n" +			//0
				"        case 22:return(la.fa);\n" +		//1npa
				"        case 23:return(la.fn);\n" +		//1npa
				"        case 24:return(la.fa.fa);\n" +		//1npa+1=2
				"        case 25:return(la.fa.fn);\n" +		//1npa+1=2
				"        case 26:return(la.fn.fa);\n" +		//1npa	
				"        case 27:return(la.fn.fn);\n" +		//1npa
				"        case 28:return(la.fa.fa.fa);\n" +	//1npa+2=3
				"        case 29:return(la.fa.fa.fn);\n" +	//1npa+2=3			
				"        case 30:return(la.fa.fn.fa);\n" +	//1npa+1=2
				"        case 31:return(la.fa.fn.fn);\n" +	//1npa+1=2			
				"        case 32:return(la.fn.fa.fa);\n" +	//1npa+1=2
				"        case 33:return(la.fn.fa.fn);\n" +	//1npa+1=2			
				"        case 34:return(la.fn.fn.fa);\n" +  //1npa
				"        case 35:return(la.fn.fn.fn);\n" +	//1npa	
				"        case 41:return(this.fa);\n" +		//0
				"        case 42:return(fa.fa);\n" +		//1
				"        case 43:return(this.fa.fn);\n" +	//1
				"        case 44:return(this.fa.fa.fa);\n" +//2
				"        case 45:return(this.fa.fa.fn);\n" +//2
				"        case 46:return(this.fa.fn.fa);\n" +//1
				"        case 47:return(this.fa.fn.fn);\n" +//1
				"        case 48:return(this.fa.fa.fa.fa);\n" +	//3
				"        case 49:return(this.fa.fa.fa.fn);\n" +	//3			
				"        case 50:return(this.fa.fa.fn.fa);\n" + //2
				"        case 51:return(this.fa.fa.fn.fn);\n" + //2				
				"        case 52:return(this.fa.fn.fa.fa);\n" + //2
				"        case 53:return(this.fa.fn.fa.fn);\n" +	//2			
				"        case 54:return(this.fa.fn.fn.fa);\n" + //1
				"        case 55:return(this.fa.fn.fn.fn);\n" +	//1  //total58	
				"        case 61:return(this.fn);\n" +		//0
				"        case 62:return(fn.fa);\n" +		//0
				"        case 63:return(this.fn.fn);\n" +	//0
				"        case 64:return(this.fn.fa.fa);\n" +//1
				"        case 65:return(this.fn.fa.fn);\n" +//1
				"        case 66:return(this.fn.fn.fa);\n" +//0
				"        case 67:return(this.fn.fn.fn);\n" +//0
				"        case 68:return(this.fn.fa.fa.fa);\n" +	//2
				"        case 69:return(this.fn.fa.fa.fn);\n" +	//2			
				"        case 70:return(this.fn.fa.fn.fa);\n" + //1
				"        case 71:return(this.fn.fa.fn.fn);\n" + //1				
				"        case 72:return(this.fn.fn.fa.fa);\n" + //1
				"        case 73:return(fn.fn.fa.fn);\n" +		//1			
				"        case 74:return(this.fn.fn.fn.fa);\n" + //0
				"        case 75:return(this.fn.fn.fn.fn);\n" +	//0  //total68				
				"        default:return (this);\n" +		
				"        }\n" + 
				"  }\n" + 
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 9)\n" + 
				"	case 4: return(ln.fa.fa);\n" + 
				"	              ^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 10)\n" + 
				"	case 5: return(ln.fa.fn);\n" + 
				"	              ^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 13)\n" + 
				"	case 8: return(ln.fa.fa.fa);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 13)\n" + 
				"	case 8: return(ln.fa.fa.fa);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 14)\n" + 
				"	case 9: return(ln.fa.fa.fn);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 14)\n" + 
				"	case 9: return(ln.fa.fa.fn);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"7. ERROR in X.java (at line 15)\n" + 
				"	case 10:return(ln.fa.fn.fa);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"8. ERROR in X.java (at line 16)\n" + 
				"	case 11:return(ln.fa.fn.fn);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"9. ERROR in X.java (at line 17)\n" + 
				"	case 12:return(ln.fn.fa.fa);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"10. ERROR in X.java (at line 18)\n" + 
				"	case 13:return(ln.fn.fa.fn);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"11. ERROR in X.java (at line 20)\n" + 
				"	case 15:return(ln.fn.fn.fn = null);\n" + 
				"	              ^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"12. ERROR in X.java (at line 22)\n" + 
				"	case 22:return(la.fa);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"13. ERROR in X.java (at line 23)\n" + 
				"	case 23:return(la.fn);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"14. ERROR in X.java (at line 24)\n" + 
				"	case 24:return(la.fa.fa);\n" + 
				"	              ^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"15. ERROR in X.java (at line 24)\n" + 
				"	case 24:return(la.fa.fa);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"16. ERROR in X.java (at line 25)\n" + 
				"	case 25:return(la.fa.fn);\n" + 
				"	              ^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"17. ERROR in X.java (at line 25)\n" + 
				"	case 25:return(la.fa.fn);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"18. ERROR in X.java (at line 26)\n" + 
				"	case 26:return(la.fn.fa);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"19. ERROR in X.java (at line 27)\n" + 
				"	case 27:return(la.fn.fn);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"20. ERROR in X.java (at line 28)\n" + 
				"	case 28:return(la.fa.fa.fa);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"21. ERROR in X.java (at line 28)\n" + 
				"	case 28:return(la.fa.fa.fa);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"22. ERROR in X.java (at line 28)\n" + 
				"	case 28:return(la.fa.fa.fa);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"23. ERROR in X.java (at line 29)\n" + 
				"	case 29:return(la.fa.fa.fn);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"24. ERROR in X.java (at line 29)\n" + 
				"	case 29:return(la.fa.fa.fn);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"25. ERROR in X.java (at line 29)\n" + 
				"	case 29:return(la.fa.fa.fn);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"26. ERROR in X.java (at line 30)\n" + 
				"	case 30:return(la.fa.fn.fa);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"27. ERROR in X.java (at line 30)\n" + 
				"	case 30:return(la.fa.fn.fa);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"28. ERROR in X.java (at line 31)\n" + 
				"	case 31:return(la.fa.fn.fn);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"29. ERROR in X.java (at line 31)\n" + 
				"	case 31:return(la.fa.fn.fn);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"30. ERROR in X.java (at line 32)\n" + 
				"	case 32:return(la.fn.fa.fa);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"31. ERROR in X.java (at line 32)\n" + 
				"	case 32:return(la.fn.fa.fa);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"32. ERROR in X.java (at line 33)\n" + 
				"	case 33:return(la.fn.fa.fn);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n" + 
				"33. ERROR in X.java (at line 33)\n" + 
				"	case 33:return(la.fn.fa.fn);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"34. ERROR in X.java (at line 34)\n" + 
				"	case 34:return(la.fn.fn.fa);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"35. ERROR in X.java (at line 35)\n" + 
				"	case 35:return(la.fn.fn.fn);\n" + 
				"	               ^^\n" + 
				"Potential null pointer access: The variable la may be null at this location\n" + 
				"----------\n" + 
				"36. ERROR in X.java (at line 37)\n" + 
				"	case 42:return(fa.fa);\n" + 
				"	              ^^^^^^^\n" + 
				"Possible null dereference at access of field fa\n" + 
				"----------\n" + 
				"37. ERROR in X.java (at line 38)\n" + 
				"	case 43:return(this.fa.fn);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"38. ERROR in X.java (at line 39)\n" + 
				"	case 44:return(this.fa.fa.fa);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"39. ERROR in X.java (at line 39)\n" + 
				"	case 44:return(this.fa.fa.fa);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"40. ERROR in X.java (at line 40)\n" + 
				"	case 45:return(this.fa.fa.fn);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"41. ERROR in X.java (at line 40)\n" + 
				"	case 45:return(this.fa.fa.fn);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"42. ERROR in X.java (at line 41)\n" + 
				"	case 46:return(this.fa.fn.fa);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"43. ERROR in X.java (at line 42)\n" + 
				"	case 47:return(this.fa.fn.fn);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"44. ERROR in X.java (at line 43)\n" + 
				"	case 48:return(this.fa.fa.fa.fa);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"45. ERROR in X.java (at line 43)\n" + 
				"	case 48:return(this.fa.fa.fa.fa);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"46. ERROR in X.java (at line 43)\n" + 
				"	case 48:return(this.fa.fa.fa.fa);\n" + 
				"	               ^^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"47. ERROR in X.java (at line 44)\n" + 
				"	case 49:return(this.fa.fa.fa.fn);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"48. ERROR in X.java (at line 44)\n" + 
				"	case 49:return(this.fa.fa.fa.fn);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"49. ERROR in X.java (at line 44)\n" + 
				"	case 49:return(this.fa.fa.fa.fn);\n" + 
				"	               ^^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"50. ERROR in X.java (at line 45)\n" + 
				"	case 50:return(this.fa.fa.fn.fa);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"51. ERROR in X.java (at line 45)\n" + 
				"	case 50:return(this.fa.fa.fn.fa);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"52. ERROR in X.java (at line 46)\n" + 
				"	case 51:return(this.fa.fa.fn.fn);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"53. ERROR in X.java (at line 46)\n" + 
				"	case 51:return(this.fa.fa.fn.fn);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"54. ERROR in X.java (at line 47)\n" + 
				"	case 52:return(this.fa.fn.fa.fa);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"55. ERROR in X.java (at line 47)\n" + 
				"	case 52:return(this.fa.fn.fa.fa);\n" + 
				"	               ^^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"56. ERROR in X.java (at line 48)\n" + 
				"	case 53:return(this.fa.fn.fa.fn);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"57. ERROR in X.java (at line 48)\n" + 
				"	case 53:return(this.fa.fn.fa.fn);\n" + 
				"	               ^^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"58. ERROR in X.java (at line 49)\n" + 
				"	case 54:return(this.fa.fn.fn.fa);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"59. ERROR in X.java (at line 50)\n" + 
				"	case 55:return(this.fa.fn.fn.fn);\n" + 
				"	               ^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"60. ERROR in X.java (at line 54)\n" + 
				"	case 64:return(this.fn.fa.fa);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"61. ERROR in X.java (at line 55)\n" + 
				"	case 65:return(this.fn.fa.fn);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"62. ERROR in X.java (at line 58)\n" + 
				"	case 68:return(this.fn.fa.fa.fa);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"63. ERROR in X.java (at line 58)\n" + 
				"	case 68:return(this.fn.fa.fa.fa);\n" + 
				"	               ^^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"64. ERROR in X.java (at line 59)\n" + 
				"	case 69:return(this.fn.fa.fa.fn);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"65. ERROR in X.java (at line 59)\n" + 
				"	case 69:return(this.fn.fa.fa.fn);\n" + 
				"	               ^^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"66. ERROR in X.java (at line 60)\n" + 
				"	case 70:return(this.fn.fa.fn.fa);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"67. ERROR in X.java (at line 61)\n" + 
				"	case 71:return(this.fn.fa.fn.fn);\n" + 
				"	               ^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"68. ERROR in X.java (at line 62)\n" + 
				"	case 72:return(this.fn.fn.fa.fa);\n" + 
				"	               ^^^^^^^^^^^^^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"69. ERROR in X.java (at line 63)\n" + 
				"	case 73:return(fn.fn.fa.fn);\n" + 
				"	              ^^^^^^^^^^^^^\n" + 
				"Possible null dereference at access of field fn\n" + 
				"----------\n");
	} 
	public void test_0107_fieldAccessRhs() {
		this.runNegativeTest(
			new String[] {
				"X.java",	
				"class X {\n" +
				"  /*@nullable*/ X a;\n"+
				"  /*@non_null*/ X n = new X();\n"+
				"	void foo(){\n"+	
				"		Object o;\n" +
				"		o = a; //ok\n"+
				"		o = n; //ok \n"+
				"\n"+
				"		o = a.a; //1 \n"+
				"		o = a.n; //1 \n"+
				"		o = n.a; //ok\n"+
				"		o = n.n; //ok\n"+
				"\n"+
				"		o = a.a.a;//2\n"+
				"		o = a.a.n;//2\n"+
				"		o = a.n.a;//1\n"+
				"		o = a.n.n;//1\n"+
				"		o = n.a.a;//1\n"+
				"		o = n.a.n;//1\n"+
				"		o = n.n.a;//ok\n"+
				"		o = n.n.n;//ok\n"+
				"	}\n"+
				"}\n"},
				"----------\n"+
				"1. ERROR in X.java (at line 9)\n"+
				"	o = a.a; //1 \n"+
				"	    ^^^\n"+
				"Possible null dereference at access of field a\n"+
				"----------\n"+
				"2. ERROR in X.java (at line 10)\n"+
				"	o = a.n; //1 \n"+
				"	    ^^^\n"+
				"Possible null dereference at access of field n\n"+
				"----------\n"+
				"3. ERROR in X.java (at line 14)\n"+
				"	o = a.a.a;//2\n"+
				"	    ^^^^^\n"+
				"Possible null dereference at access of field a\n"+
				"----------\n"+
				"4. ERROR in X.java (at line 14)\n"+
				"	o = a.a.a;//2\n"+
				"	    ^^^^^\n"+
				"Possible null dereference at access of field a\n"+
				"----------\n"+
				"5. ERROR in X.java (at line 15)\n"+
				"	o = a.a.n;//2\n"+
				"	    ^^^^^\n"+
				"Possible null dereference at access of field a\n"+
				"----------\n"+
				"6. ERROR in X.java (at line 15)\n"+
				"	o = a.a.n;//2\n"+
				"	    ^^^^^\n"+
				"Possible null dereference at access of field n\n"+
				"----------\n"+
				"7. ERROR in X.java (at line 16)\n"+
				"	o = a.n.a;//1\n"+
				"	    ^^^^^\n"+
				"Possible null dereference at access of field n\n"+
				"----------\n"+
				"8. ERROR in X.java (at line 17)\n"+
				"	o = a.n.n;//1\n"+
				"	    ^^^^^\n"+
				"Possible null dereference at access of field n\n"+
				"----------\n"+
				"9. ERROR in X.java (at line 18)\n"+
				"	o = n.a.a;//1\n"+
				"	    ^^^^^\n"+
				"Possible null dereference at access of field a\n"+
				"----------\n"+
				"10. ERROR in X.java (at line 19)\n"+
				"	o = n.a.n;//1\n"+
				"	    ^^^^^\n"+
				"Possible null dereference at access of field n\n"+
				"----------\n");
 
	}	
	public void test_0108_fieldAccessLhs() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"class X {\n" +
				"  /*@nullable*/ X a;\n"+
				"  /*@non_null*/ X n = new X();\n"+
				"  void foo() {\n" + 
				"    a = null;\n" +
				"    a.a = null;\n" +
				"    a.n = null;\n" +
				"    a.a.a = null;\n" +
				"    a.a.n = null;\n" +
				"    a.n.a = null;\n" +
				"    a.n.n = null;\n" +
				"    n = null;\n" +
				"    n.n = null;\n" +
				"    n.a = null;\n" +
				"    n.n.n = null;\n" +
				"    n.n.a = null;\n" +
				"    n.a.n = null;\n" +
				"    n.a.a = null;\n" +							
				"    Object o = java.lang.String.class;\n"+
				"  }\n" + 
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 6)\n" + 
				"	a.a = null;\n" + 
				"	^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 7)\n" + 
				"	a.n = null;\n" + 
				"	^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 7)\n" + 
				"	a.n = null;\n" + 
				"	^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 8)\n" + 
				"	a.a.a = null;\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 8)\n" + 
				"	a.a.a = null;\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 9)\n" + 
				"	a.a.n = null;\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"7. ERROR in X.java (at line 9)\n" + 
				"	a.a.n = null;\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"8. ERROR in X.java (at line 9)\n" + 
				"	a.a.n = null;\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"9. ERROR in X.java (at line 10)\n" + 
				"	a.n.a = null;\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"10. ERROR in X.java (at line 11)\n" + 
				"	a.n.n = null;\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"11. ERROR in X.java (at line 11)\n" + 
				"	a.n.n = null;\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"12. ERROR in X.java (at line 12)\n" + 
				"	n = null;\n" + 
				"	^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"13. ERROR in X.java (at line 13)\n" + 
				"	n.n = null;\n" + 
				"	^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"14. ERROR in X.java (at line 15)\n" + 
				"	n.n.n = null;\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"15. ERROR in X.java (at line 17)\n" + 
				"	n.a.n = null;\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"16. ERROR in X.java (at line 17)\n" + 
				"	n.a.n = null;\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"17. ERROR in X.java (at line 18)\n" + 
				"	n.a.a = null;\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n");
	}		
		public void test_0109_fieldAccessWithSyntaxErrors() {
			this.runNegativeTest(
				new String[] {
					"X.java",
					"import java.util.*; \n"+
					"class X {\n" +
					" 	private final /*@ non_null */ Object[][] o1; /n"+
					"	Object o2 = (Object[][])  null; /n" +
					"	void foo(/*@non_null*/Set set){\n"+
					"		Object[] o3 = set.toArray();\n"+
					"	}\n"+
					"}\n"},
					"----------\n" + 
					"1. ERROR in X.java (at line 3)\n" + 
					"	private final /*@ non_null */ Object[][] o1; /n	Object o2 = (Object[][])  null; /n	void foo(/*@non_null*/Set set){\n" + 
					"	                                             ^\n" + 
					"Syntax error on token \"/\", delete this token\n" + 
					"----------\n" + 
					"2. ERROR in X.java (at line 3)\n" + 
					"	private final /*@ non_null */ Object[][] o1; /n	Object o2 = (Object[][])  null; /n	void foo(/*@non_null*/Set set){\n" + 
					"	                                              ^\n" + 
					"Syntax error on token \"n\", nullable expected\n" + 
					"----------\n" + 
					"3. ERROR in X.java (at line 3)\n" + 
					"	private final /*@ non_null */ Object[][] o1; /n	Object o2 = (Object[][])  null; /n	void foo(/*@non_null*/Set set){\n" + 
					"	                                              ^\n" + 
					"n cannot be resolved to a type\n" + 
					"----------\n" + 
					"4. ERROR in X.java (at line 3)\n" + 
					"	private final /*@ non_null */ Object[][] o1; /n	Object o2 = (Object[][])  null; /n	void foo(/*@non_null*/Set set){\n" + 
					"	                                               	                                ^^\n" + 
					"Syntax error on tokens, delete these tokens\n" + 
					"----------\n");
	 
		}
		public void test_0110_fieldAccessNoSyntaxErrors() {
			this.runNegativeTest(
				new String[] {
					"X.java",
					"import java.util.*; \n"+
					"class X {\n" +
					" 	private final /*@ non_null */ Object[][] o1 = new Object[1][1]; \n"+
					"	Object o2 = (Object[][])  null; \n" +
					"	void foo(/*@non_null*/Set set){\n"+	
					"		Object[] o3 = set.toArray();\n"+
					"	}\n"+
					"}\n"},
					"----------\n" + 
					"1. WARNING in X.java (at line 3)\n" + 
					"	private final /*@ non_null */ Object[][] o1 = new Object[1][1]; \n" + 
					"	                                         ^^\n" + 
					"The field X.o1 is never read locally\n" + 
					"----------\n");
	 
		}				
		public void test_0111_localAccessNullableLhs() {
			this.runNegativeTest(
				new String[] {
					"X.java",
					"class X {\n" +
					"  /*@nullable*/ X a;\n"+
					"  /*@non_null*/ X n= new X();\n"+
					"  void foo(/*@nullable*/ X x) {\n" + 
					"    x.a = null;   //1*** no deref\n" +
					"    x.n = null;   //1*** no deref\n"+
					"\n" +
					"	 x.a.a = null; //1\n" +
					"	 x.a.n = null; //2\n" +
					"	 x.n.a = null; //0\n" +
					"	 x.a.n = null; //2\n"+
					"  }\n" + 
					"}"},
					"----------\n" + 
					"1. ERROR in X.java (at line 5)\n" + 
					"	x.a = null;   //1*** no deref\n" + 
					"	^\n" + 
					"Potential null pointer access: The variable x may be null at this location\n" + 
					"----------\n" + 
					"2. ERROR in X.java (at line 6)\n" + 
					"	x.n = null;   //1*** no deref\n" + 
					"	^^^^^^^^^^\n" + 
					"Possible assignment of null to an L-value declared non_null\n" + 
					"----------\n" + 
					"3. ERROR in X.java (at line 8)\n" + 
					"	x.a.a = null; //1\n" + 
					"	^^^^^\n" + 
					"Possible null dereference at access of field a\n" + 
					"----------\n" + 
					"4. ERROR in X.java (at line 9)\n" + 
					"	x.a.n = null; //2\n" + 
					"	^^^^^\n" + 
					"Possible null dereference at access of field n\n" + 
					"----------\n" + 
					"5. ERROR in X.java (at line 9)\n" + 
					"	x.a.n = null; //2\n" + 
					"	^^^^^^^^^^^^\n" + 
					"Possible assignment of null to an L-value declared non_null\n" + 
					"----------\n" + 
					"6. ERROR in X.java (at line 11)\n" + 
					"	x.a.n = null; //2\n" + 
					"	^^^^^\n" + 
					"Possible null dereference at access of field n\n" + 
					"----------\n" + 
					"7. ERROR in X.java (at line 11)\n" + 
					"	x.a.n = null; //2\n" + 
					"	^^^^^^^^^^^^\n" + 
					"Possible assignment of null to an L-value declared non_null\n" + 
					"----------\n");
	}
		public void test_0112_localAccessNullableRhs() {
			this.runNegativeTest(
				new String[] {
					"X.java",
					"class X {\n" +
					"  /*@nullable*/ X a;\n"+
					"  /*@non_null*/ X n= new X();\n"+
					"  void foo(/*@nullable*/ X x) {\n" +
					"	 Object o; \n"+
					"    o = x.a;     //1\n" +
					"    o = x.n;     //0\n" +
					"\n" +
					"	 o = x.a.a;   //1\n" +
					"	 o = x.a.n;   //1\n" +
					"	 o = x.n.a;   //0\n" +
					"	 o = x.n.n;   //0\n" +
					"\n"+
					"	 o = x.a.a.a; //2\n" +
					"	 o = x.a.a.n; //2\n" +
					"	 o = x.a.n.a; //1\n" +
					"	 o = x.a.n.n; //1\n" +
					"	 o = x.n.a.a; //1\n" +
					"	 o = x.n.a.n; //1\n" +
					"	 o = x.n.n.a; //0\n" +
					"	 o = x.n.n.n; //0\n" +
					"  }\n" + 
					"}"},
					"----------\n"+
					"1. ERROR in X.java (at line 6)\n"+
					"	o = x.a;     //1\n"+
					"	    ^\n"+
					"Potential null pointer access: The variable x may be null at this location\n"+
					"----------\n"+
					"2. ERROR in X.java (at line 9)\n"+
					"	o = x.a.a;   //1\n"+
					"	    ^^^^^\n"+
					"Possible null dereference at access of field a\n"+
					"----------\n"+
					"3. ERROR in X.java (at line 10)\n"+
					"	o = x.a.n;   //1\n"+
					"	    ^^^^^\n"+
					"Possible null dereference at access of field n\n"+
					"----------\n"+
					"4. ERROR in X.java (at line 14)\n"+
					"	o = x.a.a.a; //2\n"+
					"	    ^^^^^^^\n"+
					"Possible null dereference at access of field a\n"+
					"----------\n"+
					"5. ERROR in X.java (at line 14)\n"+
					"	o = x.a.a.a; //2\n"+
					"	    ^^^^^^^\n"+
					"Possible null dereference at access of field a\n"+
					"----------\n"+
					"6. ERROR in X.java (at line 15)\n"+
					"	o = x.a.a.n; //2\n"+
					"	    ^^^^^^^\n"+
					"Possible null dereference at access of field a\n"+
					"----------\n"+
					"7. ERROR in X.java (at line 15)\n"+
					"	o = x.a.a.n; //2\n"+
					"	    ^^^^^^^\n"+
					"Possible null dereference at access of field n\n"+
					"----------\n"+
					"8. ERROR in X.java (at line 16)\n"+
					"	o = x.a.n.a; //1\n"+
					"	    ^^^^^^^\n"+
					"Possible null dereference at access of field n\n"+
					"----------\n"+
					"9. ERROR in X.java (at line 17)\n"+
					"	o = x.a.n.n; //1\n"+
					"	    ^^^^^^^\n"+
					"Possible null dereference at access of field n\n"+
					"----------\n"+
					"10. ERROR in X.java (at line 18)\n"+
					"	o = x.n.a.a; //1\n"+
					"	    ^^^^^^^\n"+
					"Possible null dereference at access of field a\n"+
					"----------\n"+
					"11. ERROR in X.java (at line 19)\n"+
					"	o = x.n.a.n; //1\n"+
					"	    ^^^^^^^\n"+
					"Possible null dereference at access of field n\n"+
					"----------\n");
	}		
	public void test_0113_localAccessNonNullLhs() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"class X {\n"+
				"	/*@nullable*/ X a;\n"+
				"	/*@non_null*/ X n = this;\n"+
				"\n"+
				"	void foo(/*@non_null*/ X x, /*@non_null*/ Object o) {\n"+
				"		x.a   = null;\n"+
				"		x.n   = null; 	// 1 error\n"+
				"		x.a.a = null; 	// 1 error\n"+
				"		x.a.n = null; 	// 2 error\n"+
				"		x.n.a = null; 	// ok\n"+
				"		x.n.n = null; 	// 1 error\n"+
				"\n"+		
				"		x.a.a.a = null; // 2 error\n"+
				"		x.a.a.n = null; // 3 error\n"+
				"		x.a.n.a = null; // 1 error\n"+
				"		x.a.n.n = null; // 2 error\n"+
				"		x.n.a.a = null; // 1 error\n"+
				"		x.n.a.n = null; // 2 error\n"+
				"		x.n.n.a = null; // ok\n"+
				"		x.n.n.n = null; // 1 error\n"+
				"\n"+
				"		x.a   = this;  	// ok\n"+
				"		x.n   = this; 	// ok\n"+
				"		x.a.a = this; 	// 1 error\n"+
				"		x.a.n = this; 	// 1 error\n"+
				"		x.n.a = this;	// ok\n"+
				"		x.n.n = this;	// ok\n"+
				"		x.a.a.a = this; // 2 error\n"+
				"		x.a.a.n = this; // 2 error\n"+
				"		x.a.n.a = this; // 1 error\n"+
				"		x.a.n.n = this; // 1 error\n"+
				"		x.n.a.a = this; // 1 error\n"+
				"		x.n.a.n = this; // 1 error\n"+
				"		x.n.n.a = this; // ok\n"+
				"		x.n.n.n = this; // ok\n"+
				"	}\n"+
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 7)\n" + 
				"	x.n   = null; 	// 1 error\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 8)\n" + 
				"	x.a.a = null; 	// 1 error\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 9)\n" + 
				"	x.a.n = null; 	// 2 error\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 9)\n" + 
				"	x.a.n = null; 	// 2 error\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 11)\n" + 
				"	x.n.n = null; 	// 1 error\n" + 
				"	^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 13)\n" + 
				"	x.a.a.a = null; // 2 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"7. ERROR in X.java (at line 13)\n" + 
				"	x.a.a.a = null; // 2 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"8. ERROR in X.java (at line 14)\n" + 
				"	x.a.a.n = null; // 3 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"9. ERROR in X.java (at line 14)\n" + 
				"	x.a.a.n = null; // 3 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"10. ERROR in X.java (at line 14)\n" + 
				"	x.a.a.n = null; // 3 error\n" + 
				"	^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"11. ERROR in X.java (at line 15)\n" + 
				"	x.a.n.a = null; // 1 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"12. ERROR in X.java (at line 16)\n" + 
				"	x.a.n.n = null; // 2 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"13. ERROR in X.java (at line 16)\n" + 
				"	x.a.n.n = null; // 2 error\n" + 
				"	^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"14. ERROR in X.java (at line 17)\n" + 
				"	x.n.a.a = null; // 1 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"15. ERROR in X.java (at line 18)\n" + 
				"	x.n.a.n = null; // 2 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"16. ERROR in X.java (at line 18)\n" + 
				"	x.n.a.n = null; // 2 error\n" + 
				"	^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"17. ERROR in X.java (at line 20)\n" + 
				"	x.n.n.n = null; // 1 error\n" + 
				"	^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"18. ERROR in X.java (at line 24)\n" + 
				"	x.a.a = this; 	// 1 error\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"19. ERROR in X.java (at line 25)\n" + 
				"	x.a.n = this; 	// 1 error\n" + 
				"	^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"20. ERROR in X.java (at line 28)\n" + 
				"	x.a.a.a = this; // 2 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"21. ERROR in X.java (at line 28)\n" + 
				"	x.a.a.a = this; // 2 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"22. ERROR in X.java (at line 29)\n" + 
				"	x.a.a.n = this; // 2 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"23. ERROR in X.java (at line 29)\n" + 
				"	x.a.a.n = this; // 2 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"24. ERROR in X.java (at line 30)\n" + 
				"	x.a.n.a = this; // 1 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"25. ERROR in X.java (at line 31)\n" + 
				"	x.a.n.n = this; // 1 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n" + 
				"26. ERROR in X.java (at line 32)\n" + 
				"	x.n.a.a = this; // 1 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field a\n" + 
				"----------\n" + 
				"27. ERROR in X.java (at line 33)\n" + 
				"	x.n.a.n = this; // 1 error\n" + 
				"	^^^^^^^\n" + 
				"Possible null dereference at access of field n\n" + 
				"----------\n");
	}
	public void test_0114_thisQualifiedNameNullityLhs() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
				"	/*@nullable*/ X a;\n"+
				"	/*@non_null*/ X n = new X();\n"+
				"\n"+
				"	void foo() {\n"+
				"		this.a = null;		//0\n" +
				"		this.n = null;		//1\n" +
				"\n" +
				"		this.a.a = null;	//1\n" +
				"		this.a.n = null;	//2\n" +
				"		this.n.a = null;	//0\n" +
				"		this.n.n = null;	//1\n" +
				"\n" +
				"		this.a.a.a = null;	//2\n" +
				"		this.a.a.n = null;	//3\n" +
				"		this.a.n.a = null;	//1\n" +
				"		this.a.n.n = null;	//2\n" +
				"		this.n.a.a = null;	//1\n" +
				"		this.n.a.n = null;	//2\n" +
				"		this.n.n.a = null;	//0\n" +
				"		this.n.n.n = null;	//1\n" +
				"\n" +				
	            "	}\n" +
	            "}\n" 
			},
			"----------\n" + 
			"1. ERROR in X.java (at line 7)\n" + 
			"	this.n = null;		//1\n" + 
			"	^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"2. ERROR in X.java (at line 9)\n" + 
			"	this.a.a = null;	//1\n" + 
			"	^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"3. ERROR in X.java (at line 10)\n" + 
			"	this.a.n = null;	//2\n" + 
			"	^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"4. ERROR in X.java (at line 10)\n" + 
			"	this.a.n = null;	//2\n" + 
			"	^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"5. ERROR in X.java (at line 12)\n" + 
			"	this.n.n = null;	//1\n" + 
			"	^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"6. ERROR in X.java (at line 14)\n" + 
			"	this.a.a.a = null;	//2\n" + 
			"	^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"7. ERROR in X.java (at line 14)\n" + 
			"	this.a.a.a = null;	//2\n" + 
			"	^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"8. ERROR in X.java (at line 15)\n" + 
			"	this.a.a.n = null;	//3\n" + 
			"	^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"9. ERROR in X.java (at line 15)\n" + 
			"	this.a.a.n = null;	//3\n" + 
			"	^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"10. ERROR in X.java (at line 15)\n" + 
			"	this.a.a.n = null;	//3\n" + 
			"	^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"11. ERROR in X.java (at line 16)\n" + 
			"	this.a.n.a = null;	//1\n" + 
			"	^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"12. ERROR in X.java (at line 17)\n" + 
			"	this.a.n.n = null;	//2\n" + 
			"	^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"13. ERROR in X.java (at line 17)\n" + 
			"	this.a.n.n = null;	//2\n" + 
			"	^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"14. ERROR in X.java (at line 18)\n" + 
			"	this.n.a.a = null;	//1\n" + 
			"	^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"15. ERROR in X.java (at line 19)\n" + 
			"	this.n.a.n = null;	//2\n" + 
			"	^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"16. ERROR in X.java (at line 19)\n" + 
			"	this.n.a.n = null;	//2\n" + 
			"	^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"17. ERROR in X.java (at line 21)\n" + 
			"	this.n.n.n = null;	//1\n" + 
			"	^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n");
	}
	
	public void test_0115_thisQualifiedNameNullityRhs() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
				"	/*@nullable*/ X a;\n"+
				"	/*@non_null*/ X n = new X();\n"+
				"\n"+
				"	void foo() {\n"+
				"		/*@non_null*/Object o;\n"+
				"\n"+
				"		o = this.a;		//1\n" +
				"		o = this.n;		//0\n" +
				"\n" +
				"		o = this.a.a;	//2\n" +
				"		o = this.a.n;	//1\n" +
				"		o = this.n.a;	//1\n" +
				"		o = this.n.n;	//0\n" +
				"\n" +
				"		o = this.a.a.a;	//3\n" +
				"		o = this.a.a.n;	//2\n" +
				"		o = this.a.n.a;	//2\n" +
				"		o = this.a.n.n;	//1\n" +
				"		o = this.n.a.a;	//2\n" +
				"		o = this.n.a.n;	//1\n" +
				"		o = this.n.n.a;	//1\n" +
				"		o = this.n.n.n;	//0\n" +
				"\n" +				
	            "	}\n" +
	            "}\n" 
			},"----------\n" + 
			"1. ERROR in X.java (at line 8)\n" + 
			"	o = this.a;		//1\n" + 
			"	^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"2. ERROR in X.java (at line 11)\n" + 
			"	o = this.a.a;	//2\n" + 
			"	^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"3. ERROR in X.java (at line 11)\n" + 
			"	o = this.a.a;	//2\n" + 
			"	    ^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"4. ERROR in X.java (at line 12)\n" + 
			"	o = this.a.n;	//1\n" + 
			"	    ^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"5. ERROR in X.java (at line 13)\n" + 
			"	o = this.n.a;	//1\n" + 
			"	^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"6. ERROR in X.java (at line 16)\n" + 
			"	o = this.a.a.a;	//3\n" + 
			"	^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"7. ERROR in X.java (at line 16)\n" + 
			"	o = this.a.a.a;	//3\n" + 
			"	    ^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"8. ERROR in X.java (at line 16)\n" + 
			"	o = this.a.a.a;	//3\n" + 
			"	    ^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"9. ERROR in X.java (at line 17)\n" + 
			"	o = this.a.a.n;	//2\n" + 
			"	    ^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"10. ERROR in X.java (at line 17)\n" + 
			"	o = this.a.a.n;	//2\n" + 
			"	    ^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"11. ERROR in X.java (at line 18)\n" + 
			"	o = this.a.n.a;	//2\n" + 
			"	^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"12. ERROR in X.java (at line 18)\n" + 
			"	o = this.a.n.a;	//2\n" + 
			"	    ^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"13. ERROR in X.java (at line 19)\n" + 
			"	o = this.a.n.n;	//1\n" + 
			"	    ^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"14. ERROR in X.java (at line 20)\n" + 
			"	o = this.n.a.a;	//2\n" + 
			"	^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"15. ERROR in X.java (at line 20)\n" + 
			"	o = this.n.a.a;	//2\n" + 
			"	    ^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"16. ERROR in X.java (at line 21)\n" + 
			"	o = this.n.a.n;	//1\n" + 
			"	    ^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"17. ERROR in X.java (at line 22)\n" + 
			"	o = this.n.n.a;	//1\n" + 
			"	^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n");
	}
	public void test_0116a_thisQualifiedNameNullityLhs_withMethod() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
				"	/*@nullable*/ X a;\n"+
				"	/*@non_null*/ X n = new X();\n"+
				"\n"+
				"	/*@non_null*/X foo() {\n"+
				"		return this;\n" +				
	            "	}\n" +				
				"	void m() {\n"+			
				"		this.foo().a = null;\n" +		//0	
				"		this.foo().n = null;\n" +		//1
				"		this.foo().a.a.a = null;\n" +	//2
				"		this.foo().a.a.n = null;\n" +	//2
				"		this.foo().a.n.a = null;\n" +	//2
				"		this.foo().a.n.n = null;\n" +	//2
				"		this.foo().n.a.a = null;\n" +	//1
				"		this.foo().n.a.n = null;\n" +	//2
				"		this.foo().n.n.a = null;\n" +	//0
				"		this.foo().n.n.n = null;\n" +	//1
	            "	}\n" +
	            "}\n" 
			},
			"----------\n" + 
			"1. ERROR in X.java (at line 10)\n" + 
			"	this.foo().n = null;\n" + 
			"	^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"2. ERROR in X.java (at line 11)\n" + 
			"	this.foo().a.a.a = null;\n" + 
			"	^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"3. ERROR in X.java (at line 11)\n" + 
			"	this.foo().a.a.a = null;\n" + 
			"	^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"4. ERROR in X.java (at line 12)\n" + 
			"	this.foo().a.a.n = null;\n" + 
			"	^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"5. ERROR in X.java (at line 12)\n" + 
			"	this.foo().a.a.n = null;\n" + 
			"	^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"6. ERROR in X.java (at line 12)\n" + 
			"	this.foo().a.a.n = null;\n" + 
			"	^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"7. ERROR in X.java (at line 13)\n" + 
			"	this.foo().a.n.a = null;\n" + 
			"	^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"8. ERROR in X.java (at line 14)\n" + 
			"	this.foo().a.n.n = null;\n" + 
			"	^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"9. ERROR in X.java (at line 14)\n" + 
			"	this.foo().a.n.n = null;\n" + 
			"	^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"10. ERROR in X.java (at line 15)\n" + 
			"	this.foo().n.a.a = null;\n" + 
			"	^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"11. ERROR in X.java (at line 16)\n" + 
			"	this.foo().n.a.n = null;\n" + 
			"	^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"12. ERROR in X.java (at line 16)\n" + 
			"	this.foo().n.a.n = null;\n" + 
			"	^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"13. ERROR in X.java (at line 18)\n" + 
			"	this.foo().n.n.n = null;\n" + 
			"	^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n");
	}
	public void test_0116b_thisQualifiedNameNullityLhs_withMethod() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
				"	/*@nullable*/ X a;\n"+
				"	/*@non_null*/ X n = new X();\n"+
				"\n"+
				"	/*@non_null*/X foo() {\n"+
				"		return this;\n" +				
	            "	}\n" +				
				"	void m() {\n"+					
				"		this.n.a.foo().a.n.a.n.foo().a.n = null;\n"+ //5
	            "	}\n" +
	            "}\n" 
			},
			"----------\n" + 
			"1. ERROR in X.java (at line 9)\n" + 
			"	this.n.a.foo().a.n.a.n.foo().a.n = null;\n" + 
			"	^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"2. ERROR in X.java (at line 9)\n" + 
			"	this.n.a.foo().a.n.a.n.foo().a.n = null;\n" + 
			"	^^^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"3. ERROR in X.java (at line 9)\n" + 
			"	this.n.a.foo().a.n.a.n.foo().a.n = null;\n" + 
			"	^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"4. ERROR in X.java (at line 9)\n" + 
			"	this.n.a.foo().a.n.a.n.foo().a.n = null;\n" + 
			"	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"5. ERROR in X.java (at line 9)\n" + 
			"	this.n.a.foo().a.n.a.n.foo().a.n = null;\n" + 
			"	^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" );
	}
	public void test_0117_thisQualifiedNameNullityRhs_withMethod() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
				"	/*@nullable*/ X a;\n"+
				"	/*@non_null*/ X n = new X();\n"+
				"\n"+
				"	/*@non_null*/ X foo() {\n"+
				"		return this;\n" +				
	            "	}\n" +				
				"	void m() {\n"+					
				"		/*@non_null*/ Object o;\n"+
				"		o = foo();\n"+			
				"		o = this.foo();\n"+
				"\n"+
				"		o = this.foo().a;\n"+	//1
				"		o = this.foo().n;\n"+	//0
				"\n"+
				"		o = this.foo().a.a;\n"+	//2
				"		o = this.foo().a.n;\n"+	//1
				"		o = this.foo().n.a;\n"+	//1
				"		o = this.foo().n.n;\n"+	//0
				"\n"+
				"		o = this.a.n.n.a.foo().a.n.foo().a.n;\n"+	//4
				"	}\n" +
	            "}\n" 
			},"----------\n" + 
			"1. ERROR in X.java (at line 13)\n" + 
			"	o = this.foo().a;\n" + 
			"	^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"2. ERROR in X.java (at line 16)\n" + 
			"	o = this.foo().a.a;\n" + 
			"	^^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"3. ERROR in X.java (at line 16)\n" + 
			"	o = this.foo().a.a;\n" + 
			"	    ^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"4. ERROR in X.java (at line 17)\n" + 
			"	o = this.foo().a.n;\n" + 
			"	    ^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"5. ERROR in X.java (at line 18)\n" + 
			"	o = this.foo().n.a;\n" + 
			"	^^^^^^^^^^^^^^^^^^\n" + 
			"Possible assignment of null to an L-value declared non_null\n" + 
			"----------\n" + 
			"6. ERROR in X.java (at line 21)\n" + 
			"	o = this.a.n.n.a.foo().a.n.foo().a.n;\n" + 
			"	    ^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"7. ERROR in X.java (at line 21)\n" + 
			"	o = this.a.n.n.a.foo().a.n.foo().a.n;\n" + 
			"	    ^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"8. ERROR in X.java (at line 21)\n" + 
			"	o = this.a.n.n.a.foo().a.n.foo().a.n;\n" + 
			"	    ^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"9. ERROR in X.java (at line 21)\n" + 
			"	o = this.a.n.n.a.foo().a.n.foo().a.n;\n" + 
			"	    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n");
	}
	public void test_0118_thisQualifiedNameNullity_onReturn_withMethod() {
		this.runNegativeTest(
			new String[] {
				"X.java",
	            "public class X{\n" +
				"	/*@nullable*/ X a;\n"+
				"	/*@non_null*/ X n = new X();\n"+
				"\n"+
				"	/*@non_null*/ X foo() {\n"+
				"		return this;\n" +				
	            "	}\n" +				
				"	/*@non_null*/X m(int i) {\n"+					
				"		switch (i) {\n" + 
				"        	case 1: return (foo());\n" +			//0
				"        	case 2: return (this.foo());\n" +		//0
				"\n"+
				"        	case 3: return (this.foo().a);\n" +		//1
				"			case 4: return (this.foo().n);\n"+		//0
				"\n"+
				"			case 5: return (this.foo().a.a);\n"+	//2
				"			case 6: return (this.foo().a.n);\n"+	//1
				"			case 7: return (this.foo().n.a);\n"+	//1
				"			case 8: return (this.foo().n.n);\n"+	//0
				"\n"+
				"			case 9: return(this.a.n.n.a.foo().a.n.foo().a.n);\n"+	//0
				"			case 10: return(a.n.n.a.foo().a.n.foo().a.n);\n"+	//0
				"\n"+
				"			default:return (this);\n" +
				"		}\n" +
				"	}\n" +
	            "}\n" 
			},"----------\n" + 
			"1. ERROR in X.java (at line 13)\n" + 
			"	case 3: return (this.foo().a);\n" + 
			"	        ^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"The method must return a non-null result\n" + 
			"----------\n" + 
			"2. ERROR in X.java (at line 16)\n" + 
			"	case 5: return (this.foo().a.a);\n" + 
			"	        ^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"The method must return a non-null result\n" + 
			"----------\n" + 
			"3. ERROR in X.java (at line 16)\n" + 
			"	case 5: return (this.foo().a.a);\n" + 
			"	                ^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"4. ERROR in X.java (at line 17)\n" + 
			"	case 6: return (this.foo().a.n);\n" + 
			"	                ^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"5. ERROR in X.java (at line 18)\n" + 
			"	case 7: return (this.foo().n.a);\n" + 
			"	        ^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"The method must return a non-null result\n" + 
			"----------\n" + 
			"6. ERROR in X.java (at line 21)\n" + 
			"	case 9: return(this.a.n.n.a.foo().a.n.foo().a.n);\n" + 
			"	               ^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"7. ERROR in X.java (at line 21)\n" + 
			"	case 9: return(this.a.n.n.a.foo().a.n.foo().a.n);\n" + 
			"	               ^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"8. ERROR in X.java (at line 21)\n" + 
			"	case 9: return(this.a.n.n.a.foo().a.n.foo().a.n);\n" + 
			"	               ^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"9. ERROR in X.java (at line 21)\n" + 
			"	case 9: return(this.a.n.n.a.foo().a.n.foo().a.n);\n" + 
			"	               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"10. ERROR in X.java (at line 22)\n" + 
			"	case 10: return(a.n.n.a.foo().a.n.foo().a.n);\n" + 
			"	                ^^^^^^^\n" + 
			"Possible null dereference at access of field n\n" + 
			"----------\n" + 
			"11. ERROR in X.java (at line 22)\n" + 
			"	case 10: return(a.n.n.a.foo().a.n.foo().a.n);\n" + 
			"	                ^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"12. ERROR in X.java (at line 22)\n" + 
			"	case 10: return(a.n.n.a.foo().a.n.foo().a.n);\n" + 
			"	                ^^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n" + 
			"13. ERROR in X.java (at line 22)\n" + 
			"	case 10: return(a.n.n.a.foo().a.n.foo().a.n);\n" + 
			"	                ^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
			"Possible null dereference\n" + 
			"----------\n");
	}	
	public void test_0119_thisQualifiedNameNullity_parameter() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"class X {\n" +
				"  /*@nullable*/ X a;\n"+
				"  /*@non_null*/ X n= new X();\n"+
				"  /*@non_null*/ X m1() {\n"+
				"		return this;\n" +				
	            "	}\n" +	
				"  void foo(/*@non_null*/X x) {\n" + 
				"  }\n" + 
				"	void m (){\n" +
				"		foo(this);\n"+
				"		foo(this.a);\n"+
				"		foo(this.n);\n"+
				"		foo(this.a.n.a.n.a);\n"+
				"		foo(this.a.m1());\n"+
				"		foo(this.n.m1());\n"+
				"		foo(this.n.m1().a.n.a);\n"+
				"		foo(a.n.n.m1().n.m1().a.n.a);\n"+
				"	}\n"+
				"}"},"----------\n" + 
					"1. ERROR in X.java (at line 11)\n" + 
					"	foo(this.a);\n" + 
					"	^^^^^^^^^^^\n" + 
					"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, x\n" + 
					"----------\n" + 
					"2. ERROR in X.java (at line 13)\n" + 
					"	foo(this.a.n.a.n.a);\n" + 
					"	^^^^^^^^^^^^^^^^^^^\n" + 
					"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, x\n" + 
					"----------\n" + 
					"3. ERROR in X.java (at line 13)\n" + 
					"	foo(this.a.n.a.n.a);\n" + 
					"	    ^^^^^^\n" + 
					"Possible null dereference\n" + 
					"----------\n" + 
					"4. ERROR in X.java (at line 13)\n" + 
					"	foo(this.a.n.a.n.a);\n" + 
					"	    ^^^^^^^^^^\n" + 
					"Possible null dereference\n" + 
					"----------\n" + 
					"5. ERROR in X.java (at line 14)\n" + 
					"	foo(this.a.m1());\n" + 
					"	    ^^^^^^\n" + 
					"Possible null dereference\n" + 
					"----------\n" + 
					"6. ERROR in X.java (at line 16)\n" + 
					"	foo(this.n.m1().a.n.a);\n" + 
					"	^^^^^^^^^^^^^^^^^^^^^^\n" + 
					"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, x\n" + 
					"----------\n" + 
					"7. ERROR in X.java (at line 16)\n" + 
					"	foo(this.n.m1().a.n.a);\n" + 
					"	    ^^^^^^^^^^^^^\n" + 
					"Possible null dereference\n" + 
					"----------\n" + 
					"8. ERROR in X.java (at line 17)\n" + 
					"	foo(a.n.n.m1().n.m1().a.n.a);\n" + 
					"	^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
					"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, x\n" + 
					"----------\n" + 
					"9. ERROR in X.java (at line 17)\n" + 
					"	foo(a.n.n.m1().n.m1().a.n.a);\n" + 
					"	    ^^^^^\n" + 
					"Possible null dereference at access of field n\n" + 
					"----------\n" + 
					"10. ERROR in X.java (at line 17)\n" + 
					"	foo(a.n.n.m1().n.m1().a.n.a);\n" + 
					"	    ^^^^^^^^^^^^^^^^^^^\n" + 
					"Possible null dereference\n" + 
					"----------\n"
				);
	}
	public void test_0120_IncompatibleNullity_Return() {
		this.runNegativeTest(
				new String[] {
						"I.java",
						"interface I {\n" +
						"	public abstract /*@nullable*/ String m1();\n" +
						"	public abstract /*@non_null*/ String m2();\n" +
						"	public abstract String m3();\n" +
						"}",
						"J.java",
						"public class J implements I {\n" +
						"	public /*@non_null*/ String m1(){return \"test\";}\n" + //0
						"	public /*@nullable*/ String m2(){return \"test\";}\n" +	//1	
						" 	public /*@non_null*/ String m3(){return \"test\";}\n" +	//0
						"}",
						"K.java",
						"public class K implements I {\n" +
						"	public  String m1(){return \"test\";}\n" +				//0
						"	public  String m2(){return \"test\";}\n" +				//1
						"	public /*@nullable*/ String m3(){return \"test\";}\n" +	//0
						"}"
						},
						"----------\n" + 
						"1. ERROR in J.java (at line 3)\n" + 
						"	public /*@nullable*/ String m2(){return \"test\";}\n" + 
						"	                     ^^^^^^\n" + 
						"Nullity of return type of method m2 does not match that in overridden method from I\n" + 
						"----------\n" + 
						"----------\n" + 
						"1. ERROR in K.java (at line 3)\n" + 
						"	public  String m2(){return \"test\";}\n" + 
						"	        ^^^^^^\n" + 
						"Nullity of return type of method m2 does not match that in overridden method from I\n" + 
						"----------\n");
	}
	public void test_0121_IncompatibleNullity_Parameters() {
		this.runNegativeTest(
				new String[] {
						"I.java",
						"interface I {\n" +
						"	public abstract void m1(/*@nullable*/ String x) ;\n" +
						"	public abstract void m2(/*@non_null*/ String x);\n" +
						"	public abstract void m3(String x);\n" +
						"}",
						"J.java",
						"public class J implements I {\n" +
						"	public void m1(/*@non_null*/ String x){x = \"test\";}\n" +  //1
						"	public void m2(/*@nullable*/ String x){x = \"test\";}\n" +	//1	
						" 	public void m3(/*@non_null*/ String x){x = \"test\";}\n" +	//1
						"}",
						"K.java",
						"public class K implements I {\n" +
						"	public void m1(String x){x = \"test\";}\n" +				//0
						"	public void m2(String x){x = \"test\";}\n" +				//1
						"	public void m3(/*@nullable*/ String x){x = \"test\";}\n" +	//0
						"}"
						},
						"----------\n" + 
						"1. ERROR in J.java (at line 2)\n" + 
						"	public void m1(/*@non_null*/ String x){x = \"test\";}\n" + 
						"	                             ^^^^^^\n" + 
						"Nullity of parameter x does not match that in overridden method from I \n" + 
						"----------\n" + 
						"2. ERROR in J.java (at line 3)\n" + 
						"	public void m2(/*@nullable*/ String x){x = \"test\";}\n" + 
						"	                             ^^^^^^\n" + 
						"Nullity of parameter x does not match that in overridden method from I \n" + 
						"----------\n" + 
						"3. ERROR in J.java (at line 4)\n" + 
						"	public void m3(/*@non_null*/ String x){x = \"test\";}\n" + 
						"	                             ^^^^^^\n" + 
						"Nullity of parameter x does not match that in overridden method from I \n" + 
						"----------\n" + 
						"----------\n" + 
						"1. ERROR in K.java (at line 3)\n" + 
						"	public void m2(String x){x = \"test\";}\n" + 
						"	               ^^^^^^\n" + 
						"Nullity of parameter x does not match that in overridden method from I \n" + 
						"----------\n");
	}	
	public void test_0122_IncompatibleNullity_ClassLevel() {
		this.runNegativeTest(
			new String[] {
				"X.java",	
				"//@ non_null_by_default \n"+
				"class X { \n" +
				" 	String foo1(Object c1, /*@nullable*/ Object d1){ \n" +
				"		if (c1 != null && d1 != null) {	} \n" +
				"		return new String();\n"+
				"	} \n" +
				" 	/*@nullable*/Object foo2(){ return null;} \n" +				
				"}\n", 
				"Y.java", 
				"class Y extends X { \n" +
				" 	String foo1(Object c2, /*@non_null*/ Object d2){ \n" +
				"		if (c2 != null && d2 != null) {	} \n" +	
				"		return new String();\n"+
				"	} \n" +	
				" 	/*@non_null*/Object foo2(){ return null;} \n" +
				"}\n"},
				"----------\n" + 
				"1. ERROR in X.java (at line 4)\n" + 
				"	if (c1 != null && d1 != null) {	} \n" + 
				"	    ^^\n" + 
				"Redundant null check: The variable c1 cannot be null at this location\n" + 
				"----------\n" + 
				"----------\n" + 
				"1. ERROR in Y.java (at line 2)\n" + 
				"	String foo1(Object c2, /*@non_null*/ Object d2){ \n" + 
				"	^^^^^^\n" + 
				"Nullity of return type of method foo1 does not match that in overridden method from X\n" + 
				"----------\n" + 
				"2. ERROR in Y.java (at line 2)\n" + 
				"	String foo1(Object c2, /*@non_null*/ Object d2){ \n" + 
				"	            ^^^^^^\n" + 
				"Nullity of parameter c2 does not match that in overridden method from X \n" + 
				"----------\n" + 
				"3. ERROR in Y.java (at line 2)\n" + 
				"	String foo1(Object c2, /*@non_null*/ Object d2){ \n" + 
				"	                                     ^^^^^^\n" + 
				"Nullity of parameter d2 does not match that in overridden method from X \n" + 
				"----------\n" + 
				"4. ERROR in Y.java (at line 3)\n" + 
				"	if (c2 != null && d2 != null) {	} \n" + 
				"	                  ^^\n" + 
				"Redundant null check: The variable d2 cannot be null at this location\n" + 
				"----------\n" + 
				"5. ERROR in Y.java (at line 6)\n" + 
				"	/*@non_null*/Object foo2(){ return null;} \n" + 
				"	                            ^^^^^^^^^^^^\n" + 
				"The method must return a non-null result\n" + 
				"----------\n" 
				);
	}
	public void test_0123_IncompatibleNulity_StaticMethod_ReturnParam() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"public class X { \n" +
				"	public static /*@ non_null*/ Object m(Object o){return new Object();} \n" +
				"}",
				"Y.java",
				"class Y extends X{ \n" +
				"	public static Object m(/*@ non_null*/Object o){return new Object();} \n" +
				"}"},
				"");
 	}	
//	this test currently fails to display a bug: nullity checking on non-reference type
//	in this case void
	public void test_0124_IncompatibleNulity_InterfaceLevel_voidreturn() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"//@non_null_by_default \n" +
				"interface X {   \n" +
				"	 public void m(Object x) ; \n" + 
				"}  \n" +
				"interface Y extends X { \n" +
				"	 public void m(Object y) ; \n" +
				"} \n" +
				"class Z implements X { \n" +
				"	 public void m(Object z) {} \n" +
				"} \n" +
				"class Zsub extends Z { \n" +
				"	public void m(Object zsub){} \n" +
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 6)\n" + 
				"	public void m(Object y) ; \n" + 
				"	              ^^^^^^\n" + 
				"Nullity of parameter y does not match that in overridden method from X \n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 9)\n" + 
				"	public void m(Object z) {} \n" + 
				"	              ^^^^^^\n" + 
				"Nullity of parameter z does not match that in overridden method from X \n" + 
				"----------\n");
 	}	
	public void test_0130_forall_noAnnotations() {	
		Map<String, String> options = getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
		this.runNegativeTest(
			new String[] {
				"X.java",			
				"class X {\n" +
				"	void m1()  { /*@ assert (\\forall Object o;                             o.getClass() != getClass()); */} \n"+ 	//npe
				"	void m2()  { /*@ assert (\\forall Object o; true;                       o.getClass() != getClass()); */} \n"+	//npe									
				"	void m3()  { /*@ assert (\\forall Object o; o == null;                  o.getClass() != getClass()); */} \n"+ //npe
				"	void m4a() { /*@ assert (\\forall Object o; o != null;                  o.getClass() != getClass()); */} \n"+ //
				"	void m4b() { /*@ assert (\\forall Object o;                o == null || o.getClass() != getClass()); */} \n"+//
				"	void m5()  { /*@ assert (\\forall Object o; o.getClass() != getClass(); o.getClass() != getClass()); */} \n"+ //npe	
				"}\n"},
				"----------\n" + 
				"1. ERROR in X.java (at line 2)\n" + 
				"	void m1()  { /*@ assert (\\forall Object o;                             o.getClass() != getClass()); */} \n" + 
				"	                                                                       ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 3)\n" + 
				"	void m2()  { /*@ assert (\\forall Object o; true;                       o.getClass() != getClass()); */} \n" + 
				"	                                                                       ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 4)\n" + 
				"	void m3()  { /*@ assert (\\forall Object o; o == null;                  o.getClass() != getClass()); */} \n" + 
				"	                                                                       ^\n" + 
				"Null pointer access: The variable o can only be null at this location\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 7)\n" + 
				"	void m5()  { /*@ assert (\\forall Object o; o.getClass() != getClass(); o.getClass() != getClass()); */} \n" + 
				"	                                           ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n", null, true, options);
	}
	public void test_0131_forall_Annotation_nn() {
		Map<String, String> options = getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
		this.runNegativeTest(
			new String[] {
				"X.java",			
				"class X {\n" +
				"	void m1()  { /*@ assert (\\forall non_null Object o;                             o.getClass() != getClass()); */}\n"+
				"	void m2()  { /*@ assert (\\forall non_null Object o; true;                       o.getClass() != getClass()); */}\n"+										
				"	void m3()  { /*@ assert (\\forall non_null Object o; o == null;                  o.getClass() != getClass()); */}\n"+
				"	void m4a() { /*@ assert (\\forall non_null Object o; o != null;                  o.getClass() != getClass()); */}\n"+
				"	void m4b() { /*@ assert (\\forall non_null Object o;                o == null || o.getClass() != getClass()); */}\n"+
				"	void m5()  { /*@ assert (\\forall non_null Object o; o.getClass() != getClass(); o.getClass() != getClass()); */}\n"+				
				"}\n"},
				"----------\n" + 
				"1. ERROR in X.java (at line 4)\n" + 
				"	void m3()  { /*@ assert (\\forall non_null Object o; o == null;                  o.getClass() != getClass()); */}\n" + 
				"	                                                    ^\n" + 
				"Null comparison always yields false: The variable o cannot be null at this location\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 5)\n" + 
				"	void m4a() { /*@ assert (\\forall non_null Object o; o != null;                  o.getClass() != getClass()); */}\n" + 
				"	                                                    ^\n" + 
				"Redundant null check: The variable o cannot be null at this location\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 6)\n" + 
				"	void m4b() { /*@ assert (\\forall non_null Object o;                o == null || o.getClass() != getClass()); */}\n" + 
				"	                                                                   ^\n" + 
				"Null comparison always yields false: The variable o cannot be null at this location\n" + 
				"----------\n", null, true, options);
	}
	public void test_0132_forall_Annotation_able() {
		Map<String, String> options = getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
		this.runNegativeTest(
			new String[] {
				"X.java",			
				"class X {\n" +
				"	void m1()  { /*@ assert (\\forall nullable Object o;                             o.getClass() != getClass()); */}\n"+
				"	void m2()  { /*@ assert (\\forall nullable Object o; true;                       o.getClass() != getClass()); */}\n"+										
				"	void m3()  { /*@ assert (\\forall nullable Object o; o == null;                  o.getClass() != getClass()); */}\n"+
				"	void m4a() { /*@ assert (\\forall nullable Object o; o != null;                  o.getClass() != getClass()); */}\n"+
				"	void m4b() { /*@ assert (\\forall nullable Object o;                o == null || o.getClass() != getClass()); */}\n"+
				"	void m5()  { /*@ assert (\\forall nullable Object o; o.getClass() != getClass(); o.getClass() != getClass()); */}\n"+				
				"}\n"},
				"----------\n" + 
				"1. ERROR in X.java (at line 2)\n" + 
				"	void m1()  { /*@ assert (\\forall nullable Object o;                             o.getClass() != getClass()); */}\n" + 
				"	                                                                                ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 3)\n" + 
				"	void m2()  { /*@ assert (\\forall nullable Object o; true;                       o.getClass() != getClass()); */}\n" + 
				"	                                                                                ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 4)\n" + 
				"	void m3()  { /*@ assert (\\forall nullable Object o; o == null;                  o.getClass() != getClass()); */}\n" + 
				"	                                                                                ^\n" + 
				"Null pointer access: The variable o can only be null at this location\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 7)\n" + 
				"	void m5()  { /*@ assert (\\forall nullable Object o; o.getClass() != getClass(); o.getClass() != getClass()); */}\n" + 
				"	                                                    ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n", null, true, options);
	}	
	public void test_0133_forall_multiBounded_vars() {
		Map<String, String> options = getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
		this.runNegativeTest(
			new String[] {
				"X.java",			
				"class X {\n" +
				"	void m1a()  { /*@ assert (\\forall          Object c, d;                         \\typeof(c) == \\typeof(d)); */}\n"+
				"	void m1b()  { /*@ assert (\\forall non_null Object c, d;                         \\typeof(c) == \\typeof(d)); */}\n"+
				"	void m2()   { /*@ assert (\\forall          Object c, d; c != null;              \\typeof(c) == \\typeof(d)); */}\n"+										
				"	void m3a()  { /*@ assert (\\forall          Object c, d; c != null && d != null; \\typeof(c) == \\typeof(d)); */}\n"+
				" 	void m3b()	{ /*@ assert (\\forall non_null Object c, d; c != null;              \\typeof(c) == \\typeof(d)); */}\n" +
				"}\n"},
				"----------\n" + 
				"1. ERROR in X.java (at line 2)\n" + 
				"	void m1a()  { /*@ assert (\\forall          Object c, d;                         \\typeof(c) == \\typeof(d)); */}\n" + 
				"	                                                                                        ^\n" + 
				"Potential null pointer access: The variable c may be null at this location\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 2)\n" + 
				"	void m1a()  { /*@ assert (\\forall          Object c, d;                         \\typeof(c) == \\typeof(d)); */}\n" + 
				"	                                                                                                      ^\n" + 
				"Potential null pointer access: The variable d may be null at this location\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 4)\n" + 
				"	void m2()   { /*@ assert (\\forall          Object c, d; c != null;              \\typeof(c) == \\typeof(d)); */}\n" + 
				"	                                                                                                      ^\n" + 
				"Potential null pointer access: The variable d may be null at this location\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 6)\n" + 
				"	void m3b()	{ /*@ assert (\\forall non_null Object c, d; c != null;              \\typeof(c) == \\typeof(d)); */}\n" + 
				"	          	                                            ^\n" + 
				"Redundant null check: The variable c cannot be null at this location\n" + 
				"----------\n", null, true, options);		
	}	
	public void test_0134_forall_leftof_AndAnd() {
		Map<String, String> options = getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
		this.runNegativeTest(
			new String[] {
				"X.java",			
				"class X {\n" +
				"		public void m1(Object o) {\n"+
				"			o = new Object(); \n"+
				"			//@ assert ((\\forall Object c; o == null; c.getClass() != getClass()) && o.getClass() != getClass()); //1\n"+
				"		}\n"+
				"		public void m3(Object o) {\n"+
				"			//@ assert ((\\forall Object c; o == null; c.getClass() != getClass()) && o.getClass() != getClass()); //3\n"+
				"		}\n"+
				"		public void m4(Object o) {\n"+
				"			//@ assert ((\\forall Object c; o != null; c.getClass() != getClass()) && o.getClass() != getClass()); //4\n"+
				"		}\n"+
				"		public void m5(Object o) {\n"+
				"			//@ assert ((\\forall Object c; o == null && c == null; c.getClass() != getClass()) && o.getClass() != getClass()); //5\n"+
				"		}\n"+
				"		public void m6(Object o) {\n"+
				"			//@ assert ((\\forall Object c; o == null && c != null; c.getClass() != getClass()) && o.getClass() != getClass()); //6\n"+
				"		}\n"+
				"		public void m7(Object o) {\n"+
				"			//@ assert ((\\forall Object c; o != null && c == null; c.getClass() != getClass()) && o.getClass() != getClass()); //7\n"+
				"		}\n"+
				"		public void m8(Object o) {\n"+
				"			//@ assert ((\\forall Object c; o != null && c != null; c.getClass() != getClass()) && o.getClass() != getClass()); //8\n"+
				"		}\n"+
				"		public void m9(Object o) {\n"+
				"			//@ assert ((\\forall Object c; c == null && o == null; c.getClass() != getClass()) && o.getClass() != getClass()); //9\n"+
				"		}\n"+
				"		public void m11(Object o) {\n"+
				"			//@ assert ((\\forall Object c; c != null && o != null; c.getClass() != getClass()) && o.getClass() != getClass()); //11\n"+
				"		}\n"+
	
				"}\n"},
				"----------\n" + 
				"1. ERROR in X.java (at line 4)\n" + 
				"	//@ assert ((\\forall Object c; o == null; c.getClass() != getClass()) && o.getClass() != getClass()); //1\n" + 
				"	                               ^\n" + 
				"Null comparison always yields false: The variable o cannot be null at this location\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 4)\n" + 
				"	//@ assert ((\\forall Object c; o == null; c.getClass() != getClass()) && o.getClass() != getClass()); //1\n" + 
				"	                                          ^\n" + 
				"Potential null pointer access: The variable c may be null at this location\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 7)\n" + 
				"	//@ assert ((\\forall Object c; o == null; c.getClass() != getClass()) && o.getClass() != getClass()); //3\n" + 
				"	                                          ^\n" + 
				"Potential null pointer access: The variable c may be null at this location\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 7)\n" + 
				"	//@ assert ((\\forall Object c; o == null; c.getClass() != getClass()) && o.getClass() != getClass()); //3\n" + 
				"	                                                                         ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 10)\n" + 
				"	//@ assert ((\\forall Object c; o != null; c.getClass() != getClass()) && o.getClass() != getClass()); //4\n" + 
				"	                                          ^\n" + 
				"Potential null pointer access: The variable c may be null at this location\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 10)\n" + 
				"	//@ assert ((\\forall Object c; o != null; c.getClass() != getClass()) && o.getClass() != getClass()); //4\n" + 
				"	                                                                         ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"7. ERROR in X.java (at line 13)\n" + 
				"	//@ assert ((\\forall Object c; o == null && c == null; c.getClass() != getClass()) && o.getClass() != getClass()); //5\n" + 
				"	                                                       ^\n" + 
				"Null pointer access: The variable c can only be null at this location\n" + 
				"----------\n" + 
				"8. ERROR in X.java (at line 13)\n" + 
				"	//@ assert ((\\forall Object c; o == null && c == null; c.getClass() != getClass()) && o.getClass() != getClass()); //5\n" + 
				"	                                                                                      ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"9. ERROR in X.java (at line 16)\n" + 
				"	//@ assert ((\\forall Object c; o == null && c != null; c.getClass() != getClass()) && o.getClass() != getClass()); //6\n" + 
				"	                                                                                      ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"10. ERROR in X.java (at line 19)\n" + 
				"	//@ assert ((\\forall Object c; o != null && c == null; c.getClass() != getClass()) && o.getClass() != getClass()); //7\n" + 
				"	                                                       ^\n" + 
				"Null pointer access: The variable c can only be null at this location\n" + 
				"----------\n" + 
				"11. ERROR in X.java (at line 19)\n" + 
				"	//@ assert ((\\forall Object c; o != null && c == null; c.getClass() != getClass()) && o.getClass() != getClass()); //7\n" + 
				"	                                                                                      ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"12. ERROR in X.java (at line 22)\n" + 
				"	//@ assert ((\\forall Object c; o != null && c != null; c.getClass() != getClass()) && o.getClass() != getClass()); //8\n" + 
				"	                                                                                      ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"13. ERROR in X.java (at line 25)\n" + 
				"	//@ assert ((\\forall Object c; c == null && o == null; c.getClass() != getClass()) && o.getClass() != getClass()); //9\n" + 
				"	                                                       ^\n" + 
				"Null pointer access: The variable c can only be null at this location\n" + 
				"----------\n" + 
				"14. ERROR in X.java (at line 25)\n" + 
				"	//@ assert ((\\forall Object c; c == null && o == null; c.getClass() != getClass()) && o.getClass() != getClass()); //9\n" + 
				"	                                                                                      ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n" + 
				"15. ERROR in X.java (at line 28)\n" + 
				"	//@ assert ((\\forall Object c; c != null && o != null; c.getClass() != getClass()) && o.getClass() != getClass()); //11\n" + 
				"	                                                                                      ^\n" + 
				"Potential null pointer access: The variable o may be null at this location\n" + 
				"----------\n", null, true, options);
	}
	public void test_0140a_ExplicitConstructorInvokation() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"class X {\n" +				
				"	X(/*@ nullable*/Object o){} \n" +
				"}\n", 
				"Y.java",
				"class Y extends X {\n" +				
				"	Y(){super(null);} \n" +
				"}\n"				},
				"");
	}
	public void test_0140b_ExplicitConstructorInvokation() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"class X {\n" +				
				"	X(/*@ non_null*/Object o){} \n" +
				"}\n", 
				"Y.java",
				"class Y extends X {\n" +				
				"	Y(){super(null);} \n" +
				"}\n"				},
				"----------\n" + 
				"1. ERROR in Y.java (at line 2)\n" + 
				"	Y(){super(null);} \n" + 
				"	    ^^^^^^^^^^^^\n" + 
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, o\n" + 
				"----------\n");
	}	
	public void test_0141_ExplicitConstructorInvokation_AlternateConstructors() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"public class X { \n" +
				"	X(/*@ non_null*/ Object o){} \n" +
				"	X(int i){ \n" + 
				"		this(null); \n" +	
				"	} \n" +
				"	X(Object o, int i){ \n" +
				"		this(o); \n" +		
				"	} \n" +
				"	void m(){ \n" +
				"		X x = new X(null, 1); 	//0 \n" +
				"		X y = new X(null);  	//1 poss actual null param to formal param \n" +
				"	} \n"+
				"}"},
				"----------\n" + 
				"1. ERROR in X.java (at line 4)\n" + 
				"	this(null); \n" + 
				"	^^^^^^^^^^^\n" + 
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, o\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 7)\n" + 
				"	this(o); \n" + 
				"	^^^^^^^^\n" + 
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, o\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 11)\n" + 
				"	X y = new X(null);  	//1 poss actual null param to formal param \n" + 
				"	      ^^^^^^^^^^^\n" + 
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, o\n" + 
				"----------\n");
	}
	public void test_0142_ExplicitConstructorInvokation_InnerClassParent() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"public class X { \n" +
				"	class Z {\n" +
				"		public Z(/*@ non_null*/  Object o) {} \n" +
				"	} \n" +
				"}",
				"Y.java",
				"class Y extends X.Z{ \n" +
				"	Y(){new X().super(null);} \n" +
				"}"},
				"----------\n" + 
				"1. ERROR in Y.java (at line 2)\n" + 
				"	Y(){new X().super(null);} \n" + 
				"	    ^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, o\n" + 
				"----------\n");
 	}
	public void test_0150_DefaultNullity_OnInnerClass() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"//@ non_null_by_default \n" +
				"public class X { \n" +
				"	//@ non_null_by_default \n" +
				"	class Z {\n" +						
				"	} \n" +
				"}",
				},
				"----------\n" + 
				"1. ERROR in X.java (at line 1)\n" + 
				"	//@ non_null_by_default \n" + 
				"	    ^^^^^^^^^^^^^^^^^^^\n" + 
				"Illegal modifier for the class Z; only outer class default nullity annotations are permitted\n" + 
				"----------\n");
 	}	
	public void test_0151_DefaultClassNullity_MultipleClasses_Fields() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"//@ non_null_by_default \n" +
				"class X { \n" +
				"	Object x1; \n" +
				"	class inner { \n" +
				"		Object xinner; \n" +
				" 	} \n" +
				"	Object x2; \n" +
				"} \n" +
				"class Y { \n" +
				"	Object y; \n" +
				"} \n"+
				"//@ non_null_by_default \n" +
				"class Z { \n" +
				"	Object z; \n" +
				"}\n" +
				"//@ nullable_by_default \n" + 
				"class W { \n" +
				"	Object w = null; \n" +
				"	class winner { \n" +
				"		Object winner = null; \n" +
				"	} \n" +
				"}"
				},
				"----------\n" + 
				"1. ERROR in X.java (at line 3)\n" + 
				"	Object x1; \n" + 
				"	       ^^\n" + 
				"non_null field x1 may not have been explicitly initialized\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 5)\n" + 
				"	Object xinner; \n" + 
				"	       ^^^^^^\n" + 
				"non_null field xinner may not have been explicitly initialized\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 7)\n" + 
				"	Object x2; \n" + 
				"	       ^^\n" + 
				"non_null field x2 may not have been explicitly initialized\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 14)\n" + 
				"	Object z; \n" + 
				"	       ^\n" + 
				"non_null field z may not have been explicitly initialized\n" + 
				"----------\n");
 	}
	public void test_0153_DefaultClassNullity_MultipleClasses_Locals() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"//@ non_null_by_default \n" + 
				"class X {  \n" +
				"	public Object m(Object x) { \n" + 
				"		x = null;  \n" +
				"		return x; \n" +
				"	} \n" +
				"}  \n" +
				"class Y {  \n" +
				"	 public Object m(Object y) { \n" + 
				"		y = null;  \n" +
				"		return y; \n" +
				"	} \n" +
				"}  \n" +
				"class HelperNullable { \n" +
				"	X x = new X(); \n" +
				"	Y y = new Y(); \n" +
				"	Object a = x.m(null); \n" +
				"	Object b = y.m(null); \n" +
				"} \n" +
				"//@ non_null_by_default  \n" +
				"class HelperNonNullable { \n" +
				"	X x = new X(); \n" +
				"	Y y = new Y(); \n" +
				"	Object a = x.m(null); \n" +
				"	Object b = y.m(null); \n" +
				"}"
				},
				"----------\n" + 
				"1. ERROR in X.java (at line 4)\n" + 
				"	x = null;  \n" + 
				"	^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 17)\n" + 
				"	Object a = x.m(null); \n" + 
				"	           ^^^^^^^^^\n" + 
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, x\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 17)\n" + 
				"	Object a = x.m(null); \n" + 
				"	           ^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 18)\n" + 
				"	Object b = y.m(null); \n" + 
				"	           ^\n" + 
				"Possible null dereference\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 24)\n" + 
				"	Object a = x.m(null); \n" + 
				"	           ^^^^^^^^^\n" + 
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, x\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 25)\n" + 
				"	Object b = y.m(null); \n" + 
				"	       ^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n");
 	}		
	public void test_0152_DefaultClassNullity_Arrays() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"//@ non_null_by_default \n" + 
				"class X {  \n" +
				"	Object[][] arrObjsField = new Object[10][10]; \n" +
				"	void m(Object[][] arrObjsParam) { \n" +
				"		arrObjsField[1] = null; \n" +
				"		arrObjsField[1][1] = null; \n" +
				" \n" +		
				"		arrObjsParam[1][1] = null; \n" +
				"		arrObjsParam[1] = null; \n" +
				"		arrObjsParam = null; \n" +
				"	} \n" +
				"} \n"
				},
				"----------\n" + 
				"1. ERROR in X.java (at line 5)\n" + 
				"	arrObjsField[1] = null; \n" + 
				"	^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 6)\n" + 
				"	arrObjsField[1][1] = null; \n" + 
				"	^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 8)\n" + 
				"	arrObjsParam[1][1] = null; \n" + 
				"	^^^^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 9)\n" + 
				"	arrObjsParam[1] = null; \n" + 
				"	^^^^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 10)\n" + 
				"	arrObjsParam = null; \n" + 
				"	^^^^^^^^^^^^^^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n");
 	}	
	public void test_0154_DefaultNullity_OnInnerInterface() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"//@ non_null_by_default \n" +
				"public interface X { \n" +
				"	//@ non_null_by_default \n" +
				"	interface Z {\n" +						
				"	} \n" +
				"}",
				},
				"----------\n" + 
				"1. ERROR in X.java (at line 1)\n" + 
				"	//@ non_null_by_default \n" + 
				"	    ^^^^^^^^^^^^^^^^^^^\n" + 
				"Illegal modifier for the interface Z; only outer class default nullity annotations are permitted\n" + 
				"----------\n");
 	}	
	public void test_0155_DefaultInterfaceNullity_MultipleInterfaces_Fields() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"//@ non_null_by_default \n" + 
				"interface X {  \n" +
				"	Object x1 = null;  \n" +
				"	interface inner {  \n" +
				"		Object xinner = null; \n" + 
				" 	}  \n" +
				"	Object x2 = null; \n" + 
				"}  \n" +
				"interface Y {  \n" +
				"	Object y = null; \n" + 
				"}  \n" +
				"//@ non_null_by_default \n" + 
				"interface Z {  \n" +
				"	Object z = null; \n" + 
				"} \n" +
				"//@ nullable_by_default \n" + 
				"interface W {  \n" +
				"	Object w = null;  \n" +
				"	interface winner {  \n" +
				"		Object winner = null; \n" + 
				"	} \n" + 
				"}"				
				},
				"----------\n" + 
				"1. ERROR in X.java (at line 3)\n" + 
				"	Object x1 = null;  \n" + 
				"	       ^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 5)\n" + 
				"	Object xinner = null; \n" + 
				"	       ^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 7)\n" + 
				"	Object x2 = null; \n" + 
				"	       ^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 14)\n" + 
				"	Object z = null; \n" + 
				"	       ^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n");
 	}	
	public void test_0156_DefaultNullity_MixedTypes() {
		this.runNegativeTest(
			new String[] {
				"X.java",
				"//@ non_null_by_default \n" + 
				"interface X {  \n" +
				"	Object x1 = null;  \n" +
				"	class inner {  \n" +
				"		Object xinner = null; \n" + 
				" 	}  \n" +
				"	Object x2 = null; \n" + 
				"}  \n" +				
				"//@ non_null_by_default \n" + 
				"class Y {  \n" +
				"	Object y1 = null;  \n" +
				"	interface inner {  \n" +
				"		Object yinner = null; \n" + 
				" 	}  \n" +
				"	Object y2 = null; \n" + 
				"}  \n" 						
				},
				"----------\n" + 
				"1. ERROR in X.java (at line 3)\n" + 
				"	Object x1 = null;  \n" + 
				"	       ^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"2. ERROR in X.java (at line 5)\n" + 
				"	Object xinner = null; \n" + 
				"	       ^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"3. ERROR in X.java (at line 7)\n" + 
				"	Object x2 = null; \n" + 
				"	       ^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"4. ERROR in X.java (at line 11)\n" + 
				"	Object y1 = null;  \n" + 
				"	       ^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"5. ERROR in X.java (at line 13)\n" + 
				"	Object yinner = null; \n" + 
				"	       ^^^^^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n" + 
				"6. ERROR in X.java (at line 15)\n" + 
				"	Object y2 = null; \n" + 
				"	       ^^\n" + 
				"Possible assignment of null to an L-value declared non_null\n" + 
				"----------\n");
 	}	
	public void test_1000() {
		this.runNegativeTest(
				new String[] {
						"Test1000.java",
						"public class Test1000 {\n" +
						"	  void maker(/*@non_null*/ Object _o) { }\n" +
						"	  static void make(/*@non_null*/ Object _o) { }\n" +
						"	  static void m0() { make(null); }\n" +
						"}\n",
						"Test1000Helper.java",
						"public class Test1000Helper {\n" +
						"	  void m0() { (new Test1000()).maker(null); }\n" +
						"	  void m1() { Test1000.make(null); }\n" +
						"	  static void m2() { (new Test1000()).maker(null); }\n" +
						"	  static void m3() { Test1000.make(null); }\n" +
						"}\n"
				},
				"----------\n" +
				"1. ERROR in Test1000.java (at line 4)\n" +
				"	static void m0() { make(null); }\n" +
				"	                   ^^^^^^^^^^\n" +
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, _o\n" +
				"----------\n" +
				"----------\n" +
				"1. ERROR in Test1000Helper.java (at line 2)\n" +
				"	void m0() { (new Test1000()).maker(null); }\n" +
				"	            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, _o\n" +
				"----------\n" +
				"2. ERROR in Test1000Helper.java (at line 3)\n" +
				"	void m1() { Test1000.make(null); }\n" +
				"	            ^^^^^^^^^^^^^^^^^^^\n" +
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, _o\n" +
				"----------\n" +
				"3. ERROR in Test1000Helper.java (at line 4)\n" +
				"	static void m2() { (new Test1000()).maker(null); }\n" +
				"	                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, _o\n" +
				"----------\n" +
				"4. ERROR in Test1000Helper.java (at line 5)\n" +
				"	static void m3() { Test1000.make(null); }\n" +
				"	                   ^^^^^^^^^^^^^^^^^^^\n" +
				"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, _o\n" +
				"----------\n" +
				"");		
	}
	public void test_1001() {
		this.runNegativeTest(
				new String[] {
						"Test1001.java",
						"public class Test1001 {\n" +
						"	  /*@non_null*/ Object maker() { return new Object(); }\n" +
						"	  /*@nullable*/ Object nullableMaker() { return new Object(); }\n" +
						"	  static /*@non_null*/ Object make() { return new Object(); }\n" +
						"	  static /*@nullable*/ Object nullableMake() { return null; }\n" +
						"	  /*@non_null*/ Object o = maker();\n" +
						"	  static /*@non_null*/ Object static_o = make();\n" +
						"}\n",
						"Test1001Helper.java",
						"public class Test1001Helper {\n" +
						"	  /*@non_null*/ Object o1 = (new Test1001()).maker();\n" +
						"	  /*@non_null*/ Object o2 = (new Test1001()).nullableMaker(); // error\n" +
						"	  static /*@non_null*/ Object static_o1 = Test1001.make();\n" +
						"	  static /*@non_null*/ Object static_o2 = Test1001.nullableMake(); // error\n" +
						"	  /*@nullable*/ Object m0() { return (new Test1001()).nullableMaker(); }\n" +
						"	  /*@non_null*/ Object m1() { return (new Test1001()).maker(); }\n" +
						"	  /*@non_null*/ Object m2() { return (new Test1001()).nullableMaker(); } // error\n" +
						"	  /*@nullable*/ Object m3() { return Test1001.make(); }\n" +
						"}\n"
				},
				"----------\n" +
				"1. ERROR in Test1001Helper.java (at line 3)\n" +
				"	/*@non_null*/ Object o2 = (new Test1001()).nullableMaker(); // error\n" +
				"	                     ^^\n" +
				"Possible assignment of null to an L-value declared non_null\n" +
				"----------\n" +
				"2. ERROR in Test1001Helper.java (at line 5)\n" +
				"	static /*@non_null*/ Object static_o2 = Test1001.nullableMake(); // error\n" +
				"	                            ^^^^^^^^^\n" +
				"Possible assignment of null to an L-value declared non_null\n" +
				"----------\n" +
				"3. ERROR in Test1001Helper.java (at line 8)\n" +
				"	/*@non_null*/ Object m2() { return (new Test1001()).nullableMaker(); } // error\n" +
				"	                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n" +
				"The method must return a non-null result\n" +
				"----------\n" +
				"");		
	}
	public void test_1100() {
		this.runNegativeTest(
				new String[] {
						"I.java",
						"interface I {\n" +
						"	public /*@nullable*/ String m(/*@non_null*/ Object o);\n" +
						"}",
						"J.java",
						"interface J extends I {\n" +
						"	public /*@nullable*/ String n(/*@nullable*/ Object o);\n" +
						"}",
						"K.java",
						"interface K extends J {\n" +
						"	// Return type covariance is ok. Error on parameter contravariance.\n" +
						"	public /*@non_null*/ String m(/*@nullable*/ Object o);\n" +
						"}",
						"A.java",
						"public class A {\n" +
						"	public /*@nullable*/ String m(/*@non_null*/ Object o) { return \"A.m\"; }\n" +
						"}",
						"B.java",
						"public class B extends A implements J {\n" +
						"	public /*@nullable*/ String m(/*@nullable*/ Object o) { return \"B.m\"; }\n" +
						"	public /*@nullable*/ String n(/*@nullable*/ Object o) { return \"B.n\"; }\n" +
						"}",
						"C.java",
						"public class C extends A implements K {\n" +
						"	public /*@nullable*/ String m(/*@nullable*/ Object o) { return \"C.m\"; }\n" +
						"	public /*@nullable*/ String n(/*@nullable*/ Object o) { return \"C.n\"; }\n" +
						"}"
						},
						"----------\n" + 
						"1. ERROR in K.java (at line 3)\n" + 
						"	public /*@non_null*/ String m(/*@nullable*/ Object o);\n" + 
						"	                                            ^^^^^^\n" + 
						"Nullity of parameter o does not match that in overridden method from I \n" + 
						"----------\n" + 
						"----------\n" + 
						"1. ERROR in B.java (at line 2)\n" + 
						"	public /*@nullable*/ String m(/*@nullable*/ Object o) { return \"B.m\"; }\n" + 
						"	                                            ^^^^^^\n" + 
						"Nullity of parameter o does not match that in overridden method from A \n" + 
						"----------\n" + 
						"2. ERROR in B.java (at line 2)\n" + 
						"	public /*@nullable*/ String m(/*@nullable*/ Object o) { return \"B.m\"; }\n" + 
						"	                                            ^^^^^^\n" + 
						"Nullity of parameter o does not match that in overridden method from I \n" + 
						"----------\n" + 
						"----------\n" + 
						"1. ERROR in C.java (at line 2)\n" + 
						"	public /*@nullable*/ String m(/*@nullable*/ Object o) { return \"C.m\"; }\n" + 
						"	                     ^^^^^^\n" + 
						"Nullity of return type of method m does not match that in overridden method from K\n" + 
						"----------\n" + 
						"2. ERROR in C.java (at line 2)\n" + 
						"	public /*@nullable*/ String m(/*@nullable*/ Object o) { return \"C.m\"; }\n" + 
						"	                                            ^^^^^^\n" + 
						"Nullity of parameter o does not match that in overridden method from A \n" + 
						"----------\n"
						);
	}

    public void test_1200_ConstructorArg() {
		this.runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"	private X(/*@non_null*/String s) {\n" +
					"	}\n" +
					"	public void m(/*@non_null*/String s) {\n" +
					"	}\n" +
					"	public void m1() {\n" +
					"		X x = new X(null);\n" +
					"		x.m(null);\n" +
					"	}\n" +
	                "}\n"},
	        		"----------\n" + 
	        		"1. ERROR in X.java (at line 7)\n" + 
	        		"	X x = new X(null);\n" + 
	        		"	      ^^^^^^^^^^^\n" + 
	        		"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, s\n" + 
	        		"----------\n" + 
	        		"2. ERROR in X.java (at line 8)\n" + 
	        		"	x.m(null);\n" + 
	        		"	^^^^^^^^^\n" + 
	        		"Possibly null actual parameter cannot be assigned to non_null formal parameter 1, s\n" + 
	        		"----------\n");
    }

    // A bug in JML4 was highlighted by the following code. The NPE bug was
    // because we did not know that static initialization blocks are considered
    // field declarations but whose field name is null.
    public void test_1400_StaticInitIsAField_bug() throws IOException {
    	String batchCompilerOptions = "-jml -warn:+nnts";
		String source_Helper = 
			"package a;\n" +
			"public class Helper {\n" +
			"   static final /*@nullable*/String ss;" +
			"	static { ss = null; }\n" +
			"	public static /*@nullable*/String hs;\n" +
			"}\n";
		String helperPath = "a" + File.separator + "Helper" + JmlCoreTestsUtil.defaultJavaExtension();
		String source_X = 
			"package b;\n" +
			"public class X {\n" +
			"	/*@non_null*/ String s = a.Helper.hs;\n" +
			"}\n";
		String xPath = "b" + File.separator + "X" + JmlCoreTestsUtil.defaultJavaExtension();
		String[] pathAndContents = new String[] {
				helperPath,
				source_Helper,
				xPath,
				source_X
		};
		JmlCoreTestsUtil.createSourceDir(pathAndContents, SOURCE_DIRECTORY);
		// For this bug to manifest itself, the compiler must be unable to locate
		// the source file so that jml4 code looks up the source separately and
		// then does a JmlBinaryLookup.decorateBindingWithJml().
		// If a source path is given, then it is placed first in the class path
		// and hence the compiler finds the source. Hence, srcPath must be blank.
		String srcPath = ""; // must be blank for bug to show, otherwise
		String destDir = SOURCE_DIRECTORY; // use source as destination for .class files.
		String result;
		String expected="";
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + helperPath, srcPath, destDir);
		assertEquals(helperPath, expected, result);
		System.setProperty("jdt.compiler.useSingleThread", "true");
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + xPath, srcPath, destDir);
		expected="----------\n"+
				"1. WARNING in "+ destDir + File.separator + xPath +" (at line 3)\n"+
				"	/*@non_null*/ String s = a.Helper.hs;\n"+
				"	                     ^\n"+
				"Possible assignment of null to an L-value declared non_null\n"+
				"----------\n"+
				"1 problem (1 warning)";
		assertEquals(xPath + ": " + result, expected, result);
	}

	// 1500 series for tests with specs ...
    
    // The following test illustrates that reading in .jml files
    // is broken when the type being looked up is an auxiliary type
    // being used (but not defined) within a given compilation unit.
    public void test_1500_spec_for_aux_type() throws IOException {
		String batchCompilerOptions = "-jml -warn:+nnts -nullable";
		String source_Helper = 
			"public class Helper1500 {\n" +
			"	public static /*non_null in spec file*/String non;\n" +
			"}\n";
		String helperPath = "Helper1500.java";
		String source_X = 
			"public class X {\n" +
			"	/*@non_null*/ String s = Helper1500.non;\n" +
			"}\n";
		String xPath = "X.java";
		String[] pathAndContents = new String[] {
				helperPath,
				source_Helper,
				xPath,
				source_X
		};
		JmlCoreTestsUtil.createSourceDir(pathAndContents, SOURCE_DIRECTORY);
		String srcPath = ""; // must be blank for bug to show, otherwise
		String destDir = SOURCE_DIRECTORY; // use source as destination for .class files.
		String result;
		String expected="";
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + helperPath, srcPath, destDir);
		assertEquals(helperPath, expected, result);
		System.setProperty("jdt.compiler.useSingleThread", "true");
		result = this.compileAndDeploy(batchCompilerOptions, SOURCE_DIRECTORY + File.separator + xPath, srcPath, destDir);
		expected = "----------\n"+
					"1. WARNING in " + destDir + File.separator + xPath + " (at line 2)\n"+
					"	/*@non_null*/ String s = Helper1500.non;\n"+
					"	                     ^\n"+
					"Possible assignment of null to an L-value declared non_null\n"+
					"----------\n"+
					"1 problem (1 warning)";
		assertEquals(xPath + ": " + result, expected, result);
	}
	
	// TODO: write test ... to exercise that .jml files should also be picked 
	// up if in the source path (not only if in the spec path)
}
