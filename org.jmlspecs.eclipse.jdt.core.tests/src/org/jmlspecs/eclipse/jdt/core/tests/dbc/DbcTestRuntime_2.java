package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class DbcTestRuntime_2 extends AbstractRegressionTest {

	public DbcTestRuntime_2(String name) {
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
                "       }\n" +
                "       System.out.println(\"Count is \"+count);\n" +
                "	}\n" +
                 "}\n"
			   },
               "Count is 1");
	}
 
    public void test_0002_failedPre() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ requires 10 < 5;\n" +
                "   //@ ensures true;\n" +
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "java.lang.Error: precondition failed ('(10 < 5)')");
    }
	public void test_0003_failedPost() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ requires 10 >  5;\n" +
				"   //@ ensures   5 > 10;\n" +
				"   public void m() {} \n" +
				"	public static void main(String[] args) {\n" +
				"       try {\n" +
				"          new X().m();\n" +
				"       } catch (Error e) {\n" +
				"	       System.out.println(e.toString());\n" +
				"	    }\n" +
				"	}\n" +
				"}\n"
			   },
				"java.lang.Error: postcondition failed ('(5 > 10)')");
	}
	public void test_0004_goodPreAndPost() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   private int f = -100;\n" +
				"   //@ requires i > 10;\n" +
				"   //@ ensures   this.f == i;\n" +
				"   public void m(int i) { this.f = i; } \n" +
				"   public int f() { return this.f; } \n" +
				"	public static void main(String[] args) {\n" +
				"       try {\n" +
				"          new X().m(42);\n" +
				"       } catch (Error e) {\n" +
				"	       System.out.println(e.toString());\n" +
				"	    }\n" +
				"	}\n" +
				"}\n"
			   },
				"");
	}
	public void test_0005_failedResult() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ requires i < 10;\n" +
				"   //@ ensures   \\result > 10;\n" +
				"   public int m(int i) { return 0; } \n" +
				"	public static void main(String[] args) {\n" +
				"       try {\n" +
				"          new X().m(2);\n" +
				"       } catch (Error e) {\n" +
				"	       System.out.println(e.toString());\n" +
				"	    }\n" +
				"	}\n" +
				"}\n"
			   },
				"java.lang.Error: postcondition failed ('(\\result > 10)')");
	}
	public void test_0006_goodResult() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
                "	//@ requires true;\n" +
                "	//@ ensures  \\result == 42;\n" +
                "	public int m() { return 42; }\n" +
                "	public static void main(String[] args) {\n" +
                "		try {\n" +
                "		   new X().m();\n" +
                "       } catch (Error e) {\n" +
                "         System.out.println(e.toString());\n" +
                "       }\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0007_goodInvariant() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
                "	//@ invariant 32 > 10;\n" +
                "	//@ requires true;\n" +
                "	//@ ensures  \\result == 42;\n" +
                "	public int m() { return 42; }\n" +
                "	public static void main(String[] args) {\n" +
                "		try {\n" +
                "		   new X().m();\n" +
                "       } catch (Error e) {\n" +
                "         System.out.println(e.toString());\n" +
                "       }\n" +
                "	}\n" +
                 "}\n"
			   },
               "");
	}
	public void test_0008a_badInvariant_pre() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ invariant 32 < 10;\n" +
				"   //@ requires i < 10;\n" +
				"   //@ ensures   \\result > 10;\n" +
				"   public int m(int i) { return 0; } \n" +
				"	public static void main(String[] args) {\n" +
				"       try {\n" +
				"          new X().m(2);\n" +
				"       } catch (Error e) {\n" +
				"	       System.out.println(e.toString());\n" +
				"	    }\n" +
				"	}\n" +
				"}\n"
			   },
			"java.lang.Error: invariant failed ('(32 < 10)')");
	}
	public void test_0008b_badInvariant_post() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   public int x = 32;\n" +
				"   //@ invariant this.x == 32;\n" +
				"   //@ requires i < 10;\n" +
				"   //@ ensures   \\result > 10;\n" +
				"   public int m(int i) { x = 4; return 0; } \n" +
				"	public static void main(String[] args) {\n" +
				"       try {\n" +
				"          new X().m(2);\n" +
				"       } catch (Error e) {\n" +
				"	       System.out.println(e.toString());\n" +
				"	    }\n" +
				"	}\n" +
				"}\n"
			   },
		"java.lang.Error: invariant failed ('(this.x == 32)')");
	}
    public void test_0009_SpecCaseBlock() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ requires 10 < 5;\n" +
                "   //@ {| requires true; ensures true; |} \n" +
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "java.lang.Error: precondition failed ('(10 < 5)')");
    }

    public void test_0010_SpecCaseBlock() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ requires 10 < 5;\n" +
                "   //@ {| ensures true; also requires true; ensures true; |} \n" +
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "java.lang.Error: precondition failed ('(10 < 5)')");
    }

    public void test_0011_HeavyweightSpecCase() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ behavior requires 10 < 5;\n" +
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "java.lang.Error: precondition failed ('(10 < 5)')");
    }

    public void test_0012_HeavyweightSpecCase() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ behavior requires 10 < 5; also requires true; also behavior ensures true; \n" +
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "java.lang.Error: precondition failed ('(10 < 5)')");
    }

    public void test_0013_HeavyweightSpecCase() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ normal_behavior requires 10 < 5; also requires true; also exceptional_behavior requires true; \n" +
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "java.lang.Error: precondition failed ('(10 < 5)')");
    }

    public void test_0014_HeavyweightSpecCaseBritishSpelling() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ normal_behaviour requires 10 < 5; also behaviour requires true; also exceptional_behaviour requires true; \n" +
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "java.lang.Error: precondition failed ('(10 < 5)')");
    }

    public void test_0015_Invariant_no_Predicate() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ invariant ;\n" +
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ invariant ;\n" +
                "	    ^^^^^^^^^\n" +
                "Syntax error on token \"invariant\", Expression expected after this token\n" +
                "----------\n");
    }


    public void test_0016_Invariant_simple() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ invariant true;\n" + 
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "");
    }

    public void test_0017_InvariantWithNoJavaDeclarations() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ invariant true;\n" + 
                "}\n"
                },
                "");
    }

    public void test_0018_InvariantWithModifier() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ public invariant true;\n" + 
                "}\n"
                },
                "");
    }
    public void test_0019_InvariantWithModifiers() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ public static invariant true;\n" + 
                "}\n"
                },
                "");
    }
    public void test_0020_InvariantWithInvalidModifier() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ native invariant true;\n" + 
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ native invariant true;\n" +
                "	    ^^^^^^\n" +
                "Illegal modifier for the member declaration invariant; only public, protected, private & static are permitted\n" +
                "----------\n");
    }
    public void test_0021_InvariantWithInvalidModifier() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ public native invariant true;\n" + 
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ public native invariant true;\n" +
                "	    ^^^^^^^^^^^^^\n" +
                "Illegal modifier for the member declaration invariant; only public, protected, private & static are permitted\n" +
                "----------\n");
    }
    public void test_0022_InvariantWithDoubleModifiers() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ public private invariant true;\n" + 
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ public private invariant true;\n" +
                "	    ^^^^^^^^^^^^^^\n" +
                "Duplicate modifier for the member declaration invariant\n" +
                "----------\n");
    }
    
    public void test_0023_InitiallyWithNoPredicate() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ initially ;\n" +
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ initially ;\n" +
                "	    ^^^^^^^^^\n" +
                "Syntax error on token \"initially\", Expression expected after this token\n" +
                "----------\n");
    }
    
    public void test_0024_InitiallySimple() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ initially true;\n" + 
                "   public void m() {} \n" +
                "    public static void main(String[] args) {\n" +
                "       try {\n" +
                "          new X().m();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "    }\n" +
                "}\n"
                },
                "");
    }
    
    public void test_0025_InitiallyWithNoJavaDeclarations() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ initially true;\n" + 
                "}\n"
                },
                "");
    }

    public void test_0026_InitiallyWithModifier() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ public initially true;\n" + 
                "}\n"
                },
                "");
    }
    
    public void test_0027_InitiallyWithInvalidModifier() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ static initially true;\n" + 
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ static initially true;\n" +
                "	    ^^^^^^\n" +
                "Illegal modifier for the member declaration initially; only public, protected & private are permitted\n" +
                "----------\n");
    }
    
    public void test_0028_InitiallyWithValidAndInvalidModifier() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ public static initially true;\n" + 
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ public static initially true;\n" +
                "	    ^^^^^^^^^^^^^\n" +
                "Illegal modifier for the member declaration initially; only public, protected & private are permitted\n" +
                "----------\n");
    }
    
    public void test_0022_InitiallyWithDoubleVisibility() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ public protected initially true;\n" + 
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ public protected initially true;\n" +
                "	    ^^^^^^^^^^^^^^^^\n" +
                "Duplicate modifier for the member declaration initially\n" +
                "----------\n");
    }
    
	public void test_0023_GoodInitially_RAC() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
                "	//@ initially 27 > 8;\n" +
                "	public X() { }\n" +
                "	public static void main(String[] args) {\n" +
                "		try {\n" +
                "		    X x = new X();\n" +
                "       } catch (Error e) {\n" +
                "           System.out.println(e.toString());\n" +
                "       }\n" +
                "	}\n" +
                 "}\n"
				},
				"");
	}
	
	public void test_0024_BadInitially_RAC() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ initially 27 < 8;\n" +
				"   public X() { }\n" +
				"	public static void main(String[] args) {\n" +
				"       try {\n" +
				"           X x = new X();\n" +
				"       } catch (Error e) {\n" +
				"	        System.out.println(e.toString());\n" +
				"	    }\n" +
				"	}\n" +
				"}\n"
				},
				"java.lang.Error: initially failed ('(27 < 8)')");
	}
	
	public void test_0025_GoodInitiallyLaterViolated_RAC() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
				"   //@ initially z < 27;\n" +
				"   public int z;" +
				"   public X() {\n" +
				"       z = 8;\n" +
				"   }\n" +
				"   public void changeZ() {\n" +
				"       z = 27;\n" +
				"   }\n" +
				"	public static void main(String[] args) {\n" +
				"       try {\n" +
				"           X x = new X();\n" +
				"           x.changeZ();\n" +
				"       } catch (Error e) {\n" +
				"	        System.out.println(e.toString());\n" +
				"	    }\n" +
				"	}\n" +
				"}\n"
				},
				"");
	}
	
	public void test_0100_assert() {
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
	            "       }\n" +
	            "       System.out.println(\"Count is \"+count);\n" +
	            "	}\n" +
	             "}\n"
			   },
	           "Count is 1");
	}
	public void test_0101_assert() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
	            "	public static void main(String[] args) {\n" +
	            "		//@ assert true : 331;\n" +
	            "       int count = 0;\n" +
	            "       try {\n" +
	            "		//@ assert false : 332;\n" +
	            "       } catch (Throwable t) {\n" +
	            "       	System.out.println(t);\n" +
	            "       	count++;\n" +
	            "       }\n" +
	            "       System.out.println(\"Count is \"+count);\n" +
	            "	}\n" +
	             "}\n"
			   },
	           "java.lang.AssertionError: 332\n" +
	           "Count is 1");
	}
	public void test_0102_assume() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
	            "	public static void main(String[] args) {\n" +
	            "		//@ assume true;\n" +
	            "       int count = 0;\n" +
	            "       try {\n" +
	            "		//@ assume false;\n" +
	            "       } catch (Throwable t) {\n" +
	            "       	count++;\n" +
	            "       }\n" +
	            "       System.out.println(\"Count is \"+count);\n" +
	            "	}\n" +
	             "}\n"
			   },
	           "Count is 1");
	}
	public void test_0103_assume() {
		this.runConformTest( new String[] {
				"X.java",
				"public class X {\n"+
	            "	public static void main(String[] args) {\n" +
	            "		//@ assume true : 331;\n" +
	            "       int count = 0;\n" +
	            "       try {\n" +
	            "		//@ assume false : 332;\n" +
	            "       } catch (Throwable t) {\n" +
	            "       	System.out.println(t);\n" +
	            "       	count++;\n" +
	            "       }\n" +
	            "       System.out.println(\"Count is \"+count);\n" +
	            "	}\n" +
	             "}\n"
			   },
	           "java.lang.AssertionError: 332\n" +
	           "Count is 1");
	}
}
