package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class AssignableTestCompiler extends AbstractRegressionTest {

	public AssignableTestCompiler(String name) {
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

    public void test_0001_AssignableWithEmptyList() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ ensures true;\n" +
                "   //@ assignable ;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 3)\n" +
                "	//@ assignable ;\n" +
                "	    ^^^^^^^^^^\n" +
                "Syntax error on token \"assignable\", StoreRef expected after this token\n" +
                "----------\n");
    }

    public void test_0002_AssignableWithIdentifier() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   int x;\n" +
                "   //@ modifies x;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }

    public void test_0003_AssignableWithIdentifierAndEnsures() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   int x;\n" +
                "   //@ modifies x;\n" + 
                "   //@ ensures true;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }

    public void test_0004_AssignableWithIdentifiers() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   int x,y,z;\n" +
                "   //@ modifies x,y,z;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }

    public void test_0005_AssignableWithNothing() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ modifiable \\nothing;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }

    public void test_0006_AssignableWithEverything() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ modifiable \\everything;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0007_AssignableWithNot_Specified() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ modifiable \\not_specified;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0008a_AssignableWithInformalDescription() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ modifiable (* Zork rules! *);\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0008b_AssignableWithInvalidInformalDescription() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ modifiable (*);\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ modifiable (*);\n" +
                "	               ^^^\n" +
                "Syntax error on tokens, StoreRef expected instead\n" +
                "----------\n");
    }
    public void test_0008c_AssignableWithInvalidInformalDescription() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ modifiable (*;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ modifiable (*;\n" +
                "	               ^^\n" +
                "Syntax error on tokens, StoreRef expected instead\n" +
                "----------\n");
    }
    public void test_0009_AssignableWithIdentifierSuffix() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   class A {;\n" +
                "     int y;\n" +
                "   }\n" +
                "   A x;\n" +
                "   //@ modifies x.y;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0010_AssignableWithThisSuffix() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+  
                "   int i;\n" +
                "   //@ modifies X.this.i;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0011_AssignableWithWildcardSuffix() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   X x = new X();\n" +
                "   //@ modifies x.*;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0012_AssignableWithArrayExpr() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   int[] x = new int[2];\n" +
                "   //@ modifies x[0];\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0013_AssignableWithArrayRange() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   int[] x = new int[2];\n" +
                "   //@ modifies x[0 ..1];\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0014_AssignableWithArrayAll() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   int[] x = new int[2];\n" +
                "   //@ modifies x[*];\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0015_AssignableWithMultipleSuffixes() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   int[] y = new int[5];\n" +
                "   X x = new X();\n" +
                "   //@ modifies this.x.y[0 ..3];\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0016_AssignableWithArrayRange() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   int i;\n" +
                "   int[] x = new int[2];\n" +
                "   //@ modifies x[(0)..(i-1)];\n" + 
                "   public void m(int i) {} \n" +
                "}\n"
                },
                "");
    }
}
