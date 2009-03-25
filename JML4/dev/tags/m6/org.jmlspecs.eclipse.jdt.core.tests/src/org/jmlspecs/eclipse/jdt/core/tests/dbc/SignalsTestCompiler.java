package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class SignalsTestCompiler extends AbstractRegressionTest {

	public SignalsTestCompiler(String name) {
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

    public void test_0001_SignalOnlyWithEmptyList() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals_only ;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ signals_only ;\n" +
                "	    ^^^^^^^^^^^^\n" +
                "Syntax error on token \"signals_only\", ClassType expected after this token\n" +
                "----------\n");
    }
    public void test_0002_SignalOnlyWith1throwable() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals_only NullPointerException;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0003_SignalOnlyWith2throwables() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals_only NullPointerException, java.io.FileNotFoundException;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0004_SignalOnlyWithNothing() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals_only \\nothing;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0005_SignalOnlyRedundantly() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals_only_redundantly NullPointerException;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
	public void test_0006_SignalOnlyRedundantly() {
	    this.runNegativeTest( new String[] {
	            "X.java",
	            "public class X {\n"+
	            "   //@ signals_only_redundantly X;\n" + 
	            "   public void m() {} \n" +
	            "}\n"
	            },
	            "----------\n" +
	            "1. ERROR in X.java (at line 2)\n" +
	            "	//@ signals_only_redundantly X;\n" +
	            "	                             ^\n" +
	            "Type mismatch: cannot convert from X to Throwable\n" +
	            "----------\n");
	}
    public void test_0007_Signals() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals (NullPointerException);\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0008_SignalsWithIdentifier() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals (NullPointerException e);\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0009_SignalsWithPredicate() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals (NullPointerException) true;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0010_SignalsWithNotSpecified() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals (NullPointerException) \\not_specified;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
public void test_0011_SignalsWithIdentifierAndPredicate() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ signals (NullPointerException e) true;\n" + 
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
public void test_0012_SignalsWithIdentifierAndNotSpecified() {
    this.runNegativeTest( new String[] {
            "X.java",
            "public class X {\n"+
            "   //@ signals (NullPointerException e) \\not_specified;\n" + 
            "   public void m() {} \n" +
            "}\n"
            },
            "");
}
public void test_0013_SignalsWithBadThrowable() {
    this.runNegativeTest( new String[] {
            "X.java",
            "public class X {\n"+
            "   //@ signals (String);\n" + 
            "   public void m() {} \n" +
            "}\n"
            },
            "----------\n" +
            "1. ERROR in X.java (at line 2)\n" +
            "	//@ signals (String);\n" +
            "	             ^^^^^^\n" +
    		"No exception of type String can be thrown; an exception type must be a subclass of Throwable\n" + 
    		"----------\n");
}
public void test_0014_SignalsWithPredicateWithBadThrowable() {
    this.runNegativeTest( new String[] {
            "X.java",
            "public class X {\n"+
            "   //@ signals (Object) true;\n" + 
            "   public void m() {} \n" +
            "}\n"
            },
            "----------\n" +
            "1. ERROR in X.java (at line 2)\n" +
            "	//@ signals (Object) true;\n" +
            "	             ^^^^^^\n" +
    		"No exception of type Object can be thrown; an exception type must be a subclass of Throwable\n" + 
    		"----------\n");
}
public void test_0015_SignalsWithIdentifierWithBadThrowable() {
    this.runNegativeTest( new String[] {
            "X.java",
            "public class X {\n"+
            "   //@ signals (X e);\n" + 
            "   public void m() {} \n" +
            "}\n"
            },
            "----------\n" +
            "1. ERROR in X.java (at line 2)\n" +
            "	//@ signals (X e);\n" +
            "	             ^\n" +
    		"No exception of type X can be thrown; an exception type must be a subclass of Throwable\n" + 
    		"----------\n");
}
public void test_0016_SignalsWithNotSpecifiedWithBadThrowable() {
    this.runNegativeTest( new String[] {
            "X.java",
            "public class X {\n"+
            "   //@ signals (Integer) \\not_specified;\n" + 
            "   public void m() {} \n" +
            "}\n"
            },
            "----------\n" +
            "1. ERROR in X.java (at line 2)\n" +
            "	//@ signals (Integer) \\not_specified;\n" +
            "	             ^^^^^^^\n" +
    		"No exception of type Integer can be thrown; an exception type must be a subclass of Throwable\n" + 
    		"----------\n");
}
public void test_0017_SignalsWithIdentifierAndPredicateWithBadThrowable() {
    this.runNegativeTest( new String[] {
            "X.java",
            "public class X {\n"+
            "   //@ signals (Boolean e);\n" + 
            "   public void m() {} \n" +
            "}\n"
            },
            "----------\n" +
            "1. ERROR in X.java (at line 2)\n" +
            "	//@ signals (Boolean e);\n" +
            "	             ^^^^^^^\n" +
    		"No exception of type Boolean can be thrown; an exception type must be a subclass of Throwable\n" + 
    		"----------\n");
}
public void test_0018_SignalsWithIdentifierAndNotSpecifiedWithBadThrowable() {
this.runNegativeTest( new String[] {
        "X.java",
        "public class X {\n"+
        "   //@ signals (Object e) \\not_specified;\n" + 
        "   public void m() {} \n" +
        "}\n"
        },
        "----------\n" +
        "1. ERROR in X.java (at line 2)\n" +
        "	//@ signals (Object e) \\not_specified;\n" +
        "	             ^^^^^^\n" +
		"No exception of type Object can be thrown; an exception type must be a subclass of Throwable\n" + 
		"----------\n");
}
public void test_0019_SignalsWithBadPredicate() {
    this.runNegativeTest( new String[] {
            "X.java",
            "public class X {\n"+
            "   //@ signals (NullPointerException) 0;\n" + 
            "   public void m() {} \n" +
            "}\n"
            },
            "----------\n" +
            "1. ERROR in X.java (at line 2)\n" +
            "	//@ signals (NullPointerException) 0;\n" +
            "	                                   ^\n" +
    		"Type mismatch: cannot convert from int to boolean\n" + 
            "----------\n");
}
public void test_0020_SignalsWithIdentifierAndBadPredicate() {
    this.runNegativeTest( new String[] {
            "X.java",
            "public class X {\n"+
            "   //@ signals (NullPointerException e) \"hello\";\n" + 
            "   public void m() {} \n" +
            "}\n"
            },
            "----------\n" +
            "1. ERROR in X.java (at line 2)\n" +
            "	//@ signals (NullPointerException e) \"hello\";\n" +
            "	                                     ^^^^^^^\n" +
    		"Type mismatch: cannot convert from String to boolean\n" + 
            "----------\n");
}
public void test_0021_Signals_redundantly() {
    this.runNegativeTest( new String[] {
            "X.java",
            "public class X {\n"+
            "   //@ signals_redundantly (NullPointerException);\n" + 
            "   public void m() {} \n" +
            "}\n"
            },
            "");
}
}
