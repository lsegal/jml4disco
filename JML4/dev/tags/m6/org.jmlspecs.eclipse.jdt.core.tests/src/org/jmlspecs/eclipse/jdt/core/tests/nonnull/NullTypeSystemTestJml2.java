package org.jmlspecs.eclipse.jdt.core.tests.nonnull;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class NullTypeSystemTestJml2 extends AbstractRegressionTest {

	public NullTypeSystemTestJml2(String name) { 
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
    
    // deactivated until invariant and \forall are processed
    public void _test_0001_NonNull1A() {
		this.runNegativeTest(
			new String[] {
				"NonNull1A.java",
				"// Also see Nullable1.java\n" +
				"\n" +
				"public class NonNull1A {\n" +
				"    //@ invariant (\forall non_null Object o; true);\n" +
				"    //@ invariant (\forall non_null long n; true);	// error: non-null used with non-reference type\n" +
				"}\n" +
				"\n" +
				"class non_null {} // non_null is not a reserved word hence this is legal.\n" +
				"\n" +
				"class NonNull1 {\n" +
				"    //@ invariant (\\exists non_null non_null n; true);\n" +
				"    //@ invariant (\\exists nullable non_null n; true);\n" +
				"}\n" +
				"\n" +
				"// Copyright (C) 2006 Iowa State University\n" +
				"//\n" +
				"// This file is part of JML\n" +
				"//\n" +
				"// JML is free software; you can redistribute it and/or modify it under the\n" +
				"// terms of the GNU General Public License as published by the Free Software\n" +
				"// Foundation; either version 2, or (at your option) any later version.\n" +
				"//\n" +
				"// JML is distributed in the hope that it will be useful, but WITHOUT ANY\n" +
				"// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS\n" +
				"// FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more\n" +
				"// details.\n" +
				"//\n" +
				"// You should have received a copy of the GNU General Public License along\n" +
				"// with JML; see the file COPYING.  If not, write to the Free Software\n" +
				"// Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.\n"                
			},
                "----------\n" +
                "----------\n");
    }
    public void test_0002_non_null_formalParams() {
		this.runNegativeTest(
			new String[] {
				"non_null1.java",
			    "// Also see Nullable1.java\n" +
				"\n" +
				"public class non_null1 {\n" +
				"\n" +
				"    void m1(/*@ non_null @*/ Object x) {}\n" +
				"\n" +
				"    void m2(/*@ non_null @*/ int[] x) {}\n" +
				"\n" +
				"    void m3(/*@ non_null @*/ boolean x) {}	// error: non-null used with non-reference type\n" +
				"\n" +
				"    void m4(/*@ non_null @*/ byte x) {}		// error: non-null used with non-reference type\n" +
				"\n" +
				"    void m5(/*@ non_null @*/ char x) {}		// error: non-null used with non-reference type\n" +
				"\n" +
				"    void m6(/*@ non_null @*/ short x) {}	// error: non-null used with non-reference type\n" +
				"\n" +
				"    void m7(/*@ non_null @*/ int x) {}		// error: non-null used with non-reference type\n" +
				"\n" +
				"    void m8(/*@ non_null @*/ long x) {}		// error: non-null used with non-reference type\n" +
				"\n" +
				"    void m9(/*@ non_null @*/ float x) {}	// error: non-null used with non-reference type\n" +
				"\n" +
				"    void m10(/*@ non_null @*/ double x) {}	// error: non-null used with non-reference type\n" +
				"\n" +
				"    void m11(/*@ non_null @*/ Object x) {}\n" +
				"\n" +
				"    // Also see Nullabl1.java.\n" +
				"}\n" +
				"\n" +
				"// Copyright (C) 2006 Iowa State University\n" +
				"//\n" +
				"// This file is part of JML\n" +
				"//\n" +
				"// JML is free software; you can redistribute it and/or modify it under the\n" +
				"// terms of the GNU General Public License as published by the Free Software\n" +
				"// Foundation; either version 2, or (at your option) any later version.\n" +
				"//\n" +
				"// JML is distributed in the hope that it will be useful, but WITHOUT ANY\n" +
				"// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS\n" +
				"// FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more\n" +
				"// details.\n" +
				"//\n" +
				"// You should have received a copy of the GNU General Public License along\n" +
				"// with JML; see the file COPYING.  If not, write to the Free Software\n" +
				"// Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.\n"
			},
            "----------\n" +
            "1. ERROR in non_null1.java (at line 9)\n" +
            "	void m3(/*@ non_null @*/ boolean x) {}	// error: non-null used with non-reference type\n" +
            "	                         ^^^^^^^\n" +
            "Syntax error on token \"boolean\", no nullity modifier expected before this token\n" +
            "----------\n" +
            "2. ERROR in non_null1.java (at line 11)\n" +
            "	void m4(/*@ non_null @*/ byte x) {}		// error: non-null used with non-reference type\n" +
            "	                         ^^^^\n" +
            "Syntax error on token \"byte\", no nullity modifier expected before this token\n" +
            "----------\n" +
            "3. ERROR in non_null1.java (at line 13)\n" +
            "	void m5(/*@ non_null @*/ char x) {}		// error: non-null used with non-reference type\n" +
            "	                         ^^^^\n" +
            "Syntax error on token \"char\", no nullity modifier expected before this token\n" +
            "----------\n" +
            "4. ERROR in non_null1.java (at line 15)\n" +
            "	void m6(/*@ non_null @*/ short x) {}	// error: non-null used with non-reference type\n" +
            "	                         ^^^^^\n" +
            "Syntax error on token \"short\", no nullity modifier expected before this token\n" +
            "----------\n" +
            "5. ERROR in non_null1.java (at line 17)\n" +
            "	void m7(/*@ non_null @*/ int x) {}		// error: non-null used with non-reference type\n" +
            "	                         ^^^\n" +
            "Syntax error on token \"int\", no nullity modifier expected before this token\n" +
            "----------\n" +
            "6. ERROR in non_null1.java (at line 19)\n" +
            "	void m8(/*@ non_null @*/ long x) {}		// error: non-null used with non-reference type\n" +
            "	                         ^^^^\n" +
            "Syntax error on token \"long\", no nullity modifier expected before this token\n" +
            "----------\n" +
            "7. ERROR in non_null1.java (at line 21)\n" +
            "	void m9(/*@ non_null @*/ float x) {}	// error: non-null used with non-reference type\n" +
            "	                         ^^^^^\n" +
            "Syntax error on token \"float\", no nullity modifier expected before this token\n" +
            "----------\n" +
            "8. ERROR in non_null1.java (at line 23)\n" +
            "	void m10(/*@ non_null @*/ double x) {}	// error: non-null used with non-reference type\n" +
            "	                          ^^^^^^\n" +
            "Syntax error on token \"double\", no nullity modifier expected before this token\n" +
            "----------\n");
    }
    // deactivated until forall is processed
    public void _test_0003_NonNull1B() {
		this.runNegativeTest(
			new String[] {
				"NonNull1B.java",
				"// Also see NonNull1B.java\n" +
				"\n" +
				"public class NonNull1B {\n" +
				"\n" +
				"    /*@ forall Object o1;\n" +
				"      @ forall non_null Object o2;\n" +
				"      @ requires true;\n" +
				"      @*/\n" +
				"    void mForAllObject() {}\n" +
				"\n" +
				"    /*@ forall int i1;\n" +
				"      @ forall non_null int i2;		// error: non-null used with non-reference type\n" +
				"      @ requires true;\n" +
				"      @*/\n" +
				"    void mForAllInt() {}\n" +
				"}\n" +
				"\n" +
				"// @(#)$Id: NullTypeSystemTestJml2.java,v 1.1 2007/07/03 19:26:16 p_jame Exp $\n" +
				"//\n" +
				"// Copyright (C) 2006 Iowa State University\n" +
				"//\n" +
				"// This file is part of JML\n" +
				"//\n" +
				"// JML is free software; you can redistribute it and/or modify it under the\n" +
				"// terms of the GNU General Public License as published by the Free Software\n" +
				"// Foundation; either version 2, or (at your option) any later version.\n" +
				"//\n" +
				"// JML is distributed in the hope that it will be useful, but WITHOUT ANY\n" +
				"// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS\n" +
				"// FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more\n" +
				"// details.\n" +
				"//\n" +
				"// You should have received a copy of the GNU General Public License along\n" +
				"// with JML; see the file COPYING.  If not, write to the Free Software\n" +
				"// Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.\n"
		},
	    "----------\n" +
	    "1. ERROR in non_null1.java (at line 3)\n" +
	    "----------\n");
	}
    // deactivated until old is processed
    public void _test_0004_NonNull1Old() {
		this.runNegativeTest(
			new String[] {
				"NonNull1B.java",
				"// Also see Nullable1.java\n" +
				"\n" +
				"public class NonNull1Old {\n" +
				"\n" +
				"    /*@ old Object o1 = \"\";\n" +
				"      @ old non_null Object o2 = \"\";\n" +
				"      @ requires true;\n" +
				"      @*/\n" +
				"    void mOldObject() {}\n" +
				"\n" +
				"    /*@ old long n1 = 0;\n" +
				"      @ old non_null long n2 = 0;	// error: non-null used with non-reference type\n" +
				"      @ requires true;\n" +
				"      @*/\n" +
				"    void mOldLong() {}\n" +
				"}\n" +
				"\n" +
				"// @(#)$Id: NullTypeSystemTestJml2.java,v 1.1 2007/07/03 19:26:16 p_jame Exp $\n" +
				"//\n" +
				"// Copyright (C) 2006 Iowa State University\n" +
				"//\n" +
				"// This file is part of JML\n" +
				"//\n" +
				"// JML is free software; you can redistribute it and/or modify it under the\n" +
				"// terms of the GNU General Public License as published by the Free Software\n" +
				"// Foundation; either version 2, or (at your option) any later version.\n" +
				"//\n" +
				"// JML is distributed in the hope that it will be useful, but WITHOUT ANY\n" +
				"// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS\n" +
				"// FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more\n" +
				"// details.\n" +
				"//\n" +
				"// You should have received a copy of the GNU General Public License along\n" +
				"// with JML; see the file COPYING.  If not, write to the Free Software\n" +
				"// Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.\n"
			},
	    "----------\n" +
	    "1. ERROR in non_null1.java (at line 3)\n" +
	    "----------\n");
    }
    // deactivated until requires is processed
    public void _test_0005_NonNull1S() {
		this.runNegativeTest(
			new String[] {
				"NonNull1S.java",
				"// Also see Nullable1.java\n" +
				"\n" +
				"public class NonNull1X {\n" +
				"\n" +
				"    java.util.Collection c;\n" +
				"\n" +
				"    //@ requires new JMLObjectSet { Integer i | c.contains(i) && true }.int_size() == 5;\n" +
				"    //@ requires new JMLObjectSet { non_null Integer i | c.contains(i) && true }.int_size() == 5;\n" +
				"    //@ requires new JMLObjectSet { nullable Integer i | c.contains(i) && true }.int_size() == 5;\n" +
				"    void mSetComp() {}\n" +
				"\n" +
				"    //@ requires new JMLObjectSet { int i | c.contains(i) && true }.int_size() == 5; // error\n" +
				"    void mSetComp2() {}\n" +
				"}\n" +
				"\n" +
				"// @(#)$Id: NullTypeSystemTestJml2.java,v 1.1 2007/07/03 19:26:16 p_jame Exp $\n" +
				"//\n" +
				"// Copyright (C) 2006 Iowa State University\n" +
				"//\n" +
				"// This file is part of JML\n" +
				"//\n" +
				"// JML is free software; you can redistribute it and/or modify it under the\n" +
				"// terms of the GNU General Public License as published by the Free Software\n" +
				"// Foundation; either version 2, or (at your option) any later version.\n" +
				"//\n" +
				"// JML is distributed in the hope that it will be useful, but WITHOUT ANY\n" +
				"// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS\n" +
				"// FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more\n" +
				"// details.\n" +
				"//\n" +
				"// You should have received a copy of the GNU General Public License along\n" +
				"// with JML; see the file COPYING.  If not, write to the Free Software\n" +
				"// Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.\n" 
			},
		"----------\n" +
		"1. ERROR in non_null1.java (at line 3)\n" +
		"----------\n");
    }
    // deactivated until invariant, \forall, and non_null pushback is processed
    public void _test_0006_NonNull1X() {
		this.runNegativeTest(
			new String[] {
				"NonNull1B.java",
				"// Also see Nullable1.java\n" +
				"\n" +
				"import org.jmlspecs.models.*;\n" +
				"\n" +
				"class non_null {} // non_null is not a reserved word hence this is legal.\n" +
				"\n" +
				"public class NonNull1X {\n" +
				"    //@ invariant (\\exists non_null non_null n; true);\n" +
				"    //@ invariant (\\forall non_null o; true);	// error, even though non_null is a type\n" +
				"}\n" +
				"\n" +
				"// @(#)$Id: NullTypeSystemTestJml2.java,v 1.1 2007/07/03 19:26:16 p_jame Exp $\n" +
				"//\n" +
				"// Copyright (C) 2006 Iowa State University\n" +
				"//\n" +
				"// This file is part of JML\n" +
				"//\n" +
				"// JML is free software; you can redistribute it and/or modify it under the\n" +
				"// terms of the GNU General Public License as published by the Free Software\n" +
				"// Foundation; either version 2, or (at your option) any later version.\n" +
				"//\n" +
				"// JML is distributed in the hope that it will be useful, but WITHOUT ANY\n" +
				"// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS\n" +
				"// FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more\n" +
				"// details.\n" +
				"//\n" +
				"// You should have received a copy of the GNU General Public License along\n" +
				"// with JML; see the file COPYING.  If not, write to the Free Software\n" +
				"// Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.\n" 
			},
			"----------\n" +
			"1. ERROR in non_null1.java (at line 3)\n" +
			"----------\n");
    }

    public void test_0007_NonNull2_interface_fields() {
		this.runNegativeTest(
			new String[] {
				"NonNull2I.java",
				"public interface NonNull2I {\n" +
				"\n" +
				"    /*@ non_null @*/ void x0;\n" +
				"\n" +
				"    /*@ non_null @*/ Object x1;\n" +
				"\n" +
				"    /*@ non_null @*/ int[] x2;\n" +
				"\n" +
				"    /*@ non_null @*/ boolean x3;\n" +
				"\n" +
				"    /*@ non_null @*/ byte x4;\n" +
				"\n" +
				"    /*@ non_null @*/ char x5;\n" +
				"\n" +
				"    /*@ non_null @*/ short x6;\n" +
				"\n" +
				"    /*@ non_null @*/ int x7;\n" +
				"\n" +
				"    /*@ non_null @*/ long x8;\n" +
				"\n" +
				"    /*@ non_null @*/ float x9;\n" +
				"\n" +
				"    /*@ non_null @*/ double x10;\n" +
				"}\n"
			},
			"----------\n" +
			"1. ERROR in NonNull2I.java (at line 3)\n" +
			"	/*@ non_null @*/ void x0;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"void\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"2. ERROR in NonNull2I.java (at line 3)\n" +
			"	/*@ non_null @*/ void x0;\n" +
			"	                      ^^\n" +
			"void is an invalid type for the variable x0\n" +
			"----------\n" +
			"3. ERROR in NonNull2I.java (at line 9)\n" +
			"	/*@ non_null @*/ boolean x3;\n" +
			"	                 ^^^^^^^\n" +
			"Syntax error on token \"boolean\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"4. ERROR in NonNull2I.java (at line 11)\n" +
			"	/*@ non_null @*/ byte x4;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"byte\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"5. ERROR in NonNull2I.java (at line 13)\n" +
			"	/*@ non_null @*/ char x5;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"char\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"6. ERROR in NonNull2I.java (at line 15)\n" +
			"	/*@ non_null @*/ short x6;\n" +
			"	                 ^^^^^\n" +
			"Syntax error on token \"short\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"7. ERROR in NonNull2I.java (at line 17)\n" +
			"	/*@ non_null @*/ int x7;\n" +
			"	                 ^^^\n" +
			"Syntax error on token \"int\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"8. ERROR in NonNull2I.java (at line 19)\n" +
			"	/*@ non_null @*/ long x8;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"long\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"9. ERROR in NonNull2I.java (at line 21)\n" +
			"	/*@ non_null @*/ float x9;\n" +
			"	                 ^^^^^\n" +
			"Syntax error on token \"float\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"10. ERROR in NonNull2I.java (at line 23)\n" +
			"	/*@ non_null @*/ double x10;\n" +
			"	                 ^^^^^^\n" +
   			"Syntax error on token \"double\", no nullity modifier expected before this token\n" +
			"----------\n");
    }
    public void test_0008_non_null_fields() {
		this.runNegativeTest(
			new String[] {
				"non_null2.java",
				"public class non_null2 {\n" +
				"\n" +
				"    /*@ non_null @*/ void x0;\n" +
				"\n" +
				"    /*@ non_null @*/ Object x1;\n" +
				"\n" +
				"    /*@ non_null @*/ int[] x2;\n" +
				"\n" +
				"    /*@ non_null @*/ boolean x3;\n" +
				"\n" +
				"    /*@ non_null @*/ byte x4;\n" +
				"\n" +
				"    /*@ non_null @*/ char x5;\n" +
				"\n" +
				"    /*@ non_null @*/ short x6;\n" +
				"\n" +
				"    /*@ non_null @*/ int x7;\n" +
				"\n" +
				"    /*@ non_null @*/ long x8;\n" +
				"\n" +
				"    /*@ non_null @*/ float x9;\n" +
				"\n" +
				"    /*@ non_null @*/ double x10;\n" +
				"}\n"
			},
			"----------\n" +
			"1. ERROR in non_null2.java (at line 3)\n" +
			"	/*@ non_null @*/ void x0;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"void\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"2. ERROR in non_null2.java (at line 3)\n" +
			"	/*@ non_null @*/ void x0;\n" +
			"	                      ^^\n" +
			"void is an invalid type for the variable x0\n" +
			"----------\n" +
			"3. ERROR in non_null2.java (at line 9)\n" +
			"	/*@ non_null @*/ boolean x3;\n" +
			"	                 ^^^^^^^\n" +
			"Syntax error on token \"boolean\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"4. ERROR in non_null2.java (at line 11)\n" +
			"	/*@ non_null @*/ byte x4;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"byte\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"5. ERROR in non_null2.java (at line 13)\n" +
			"	/*@ non_null @*/ char x5;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"char\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"6. ERROR in non_null2.java (at line 15)\n" +
			"	/*@ non_null @*/ short x6;\n" +
			"	                 ^^^^^\n" +
			"Syntax error on token \"short\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"7. ERROR in non_null2.java (at line 17)\n" +
			"	/*@ non_null @*/ int x7;\n" +
			"	                 ^^^\n" +
			"Syntax error on token \"int\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"8. ERROR in non_null2.java (at line 19)\n" +
			"	/*@ non_null @*/ long x8;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"long\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"9. ERROR in non_null2.java (at line 21)\n" +
			"	/*@ non_null @*/ float x9;\n" +
			"	                 ^^^^^\n" +
			"Syntax error on token \"float\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"10. ERROR in non_null2.java (at line 23)\n" +
			"	/*@ non_null @*/ double x10;\n" +
			"	                 ^^^^^^\n" +
   			"Syntax error on token \"double\", no nullity modifier expected before this token\n" +
			"----------\n");
    }
    public void test_0009_non_null_returnTypes() {
		this.runNegativeTest(
			new String[] {
				"non_null2.java",
				"public class non_null2 {\n" +
				"\n" +
				"    /*@ non_null @*/ void x0(){}\n" +
				"\n" +
				"    /*@ non_null @*/ Object x1(){return this;}\n" +
				"\n" +
				"    /*@ non_null @*/ int[] x2(){return new int[0];}\n" +
				"\n" +
				"    /*@ non_null @*/ boolean x3(){return true;}\n" +
				"\n" +
				"    /*@ non_null @*/ byte x4(){return 0;}\n" +
				"\n" +
				"    /*@ non_null @*/ char x5(){return 0;}\n" +
				"\n" +
				"    /*@ non_null @*/ short x6(){return 0;}\n" +
				"\n" +
				"    /*@ non_null @*/ int x7(){return 0;}\n" +
				"\n" +
				"    /*@ non_null @*/ long x8(){return 0;}\n" +
				"\n" +
				"    /*@ non_null @*/ float x9(){return 0;}\n" +
				"\n" +
				"    /*@ non_null @*/ double x10(){return 0;}\n" +
				"}\n"
			},
			"----------\n" +
			"1. ERROR in non_null2.java (at line 3)\n" +
			"	/*@ non_null @*/ void x0(){}\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"void\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"2. ERROR in non_null2.java (at line 9)\n" +
			"	/*@ non_null @*/ boolean x3(){return true;}\n" +
			"	                 ^^^^^^^\n" +
			"Syntax error on token \"boolean\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"3. ERROR in non_null2.java (at line 11)\n" +
			"	/*@ non_null @*/ byte x4(){return 0;}\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"byte\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"4. ERROR in non_null2.java (at line 13)\n" +
			"	/*@ non_null @*/ char x5(){return 0;}\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"char\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"5. ERROR in non_null2.java (at line 15)\n" +
			"	/*@ non_null @*/ short x6(){return 0;}\n" +
			"	                 ^^^^^\n" +
			"Syntax error on token \"short\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"6. ERROR in non_null2.java (at line 17)\n" +
			"	/*@ non_null @*/ int x7(){return 0;}\n" +
			"	                 ^^^\n" +
			"Syntax error on token \"int\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"7. ERROR in non_null2.java (at line 19)\n" +
			"	/*@ non_null @*/ long x8(){return 0;}\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"long\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"8. ERROR in non_null2.java (at line 21)\n" +
			"	/*@ non_null @*/ float x9(){return 0;}\n" +
			"	                 ^^^^^\n" +
			"Syntax error on token \"float\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"9. ERROR in non_null2.java (at line 23)\n" +
			"	/*@ non_null @*/ double x10(){return 0;}\n" +
			"	                 ^^^^^^\n" +
   			"Syntax error on token \"double\", no nullity modifier expected before this token\n" +
			"----------\n");
    }
    public void test_0010_non_null_locals() {
		this.runNegativeTest(
			new String[] {
				"non_null2.java",
				"public class non_null2 {\n" +
				"  void m() {\n" +
				"    /*@ non_null @*/ void x0;\n" +
				"\n" +
				"    /*@ non_null @*/ Object x1;\n" +
				"\n" +
				"    /*@ non_null @*/ int[] x2;\n" +
				"\n" +
				"    /*@ non_null @*/ boolean x3;\n" +
				"\n" +
				"    /*@ non_null @*/ byte x4;\n" +
				"\n" +
				"    /*@ non_null @*/ char x5;\n" +
				"\n" +
				"    /*@ non_null @*/ short x6;\n" +
				"\n" +
				"    /*@ non_null @*/ int x7;\n" +
				"\n" +
				"    /*@ non_null @*/ long x8;\n" +
				"\n" +
				"    /*@ non_null @*/ float x9;\n" +
				"\n" +
				"    /*@ non_null @*/ double x10;\n" +
				" }\n" +
				"}\n"
			},
			"----------\n" +
			"1. ERROR in non_null2.java (at line 3)\n" +
			"	/*@ non_null @*/ void x0;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"void\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"2. ERROR in non_null2.java (at line 3)\n" +
			"	/*@ non_null @*/ void x0;\n" +
			"	                      ^^\n" +
			"void is an invalid type for the variable x0\n" +
			"----------\n" +
			"3. ERROR in non_null2.java (at line 9)\n" +
			"	/*@ non_null @*/ boolean x3;\n" +
			"	                 ^^^^^^^\n" +
			"Syntax error on token \"boolean\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"4. ERROR in non_null2.java (at line 11)\n" +
			"	/*@ non_null @*/ byte x4;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"byte\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"5. ERROR in non_null2.java (at line 13)\n" +
			"	/*@ non_null @*/ char x5;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"char\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"6. ERROR in non_null2.java (at line 15)\n" +
			"	/*@ non_null @*/ short x6;\n" +
			"	                 ^^^^^\n" +
			"Syntax error on token \"short\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"7. ERROR in non_null2.java (at line 17)\n" +
			"	/*@ non_null @*/ int x7;\n" +
			"	                 ^^^\n" +
			"Syntax error on token \"int\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"8. ERROR in non_null2.java (at line 19)\n" +
			"	/*@ non_null @*/ long x8;\n" +
			"	                 ^^^^\n" +
			"Syntax error on token \"long\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"9. ERROR in non_null2.java (at line 21)\n" +
			"	/*@ non_null @*/ float x9;\n" +
			"	                 ^^^^^\n" +
			"Syntax error on token \"float\", no nullity modifier expected before this token\n" +
			"----------\n" +
			"10. ERROR in non_null2.java (at line 23)\n" +
			"	/*@ non_null @*/ double x10;\n" +
			"	                 ^^^^^^\n" +
   			"Syntax error on token \"double\", no nullity modifier expected before this token\n" +
			"----------\n");
    }
}	
