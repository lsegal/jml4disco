package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class DbcTestCompiler extends AbstractRegressionTest {

	// While running tests we do not have access to the workspace, hence the follow cannot be used:
	// ResourcesPlugin.getWorkspace().getRoot().getLocation().toString();
	// For now, ".." seems to be the next best solution.
	public final String workspace = "..";
	public final String path2jml4runtime = workspace + "/org.jmlspecs.jml4.runtime/bin";

	public DbcTestCompiler(String name) {
		super(name);
	}

	/** Alter the default classpath used for tests in the class by appending 
	 * the path to the directory containing the JML4 runtime classes.  If you would prefer not altering the classpath
	 * for all tests, you can always do it on a per class basis; e.g.
	 * <code>
		public final String[] jml4runtime = new String[]{path2jml4runtime};
		public void test_0029_instance() {
   			runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   //...\n" +
					"}\n",
				},
				"",
				Util.concatWithClassLibs(jml4runtime, false),
				true);
		}
	 * </code> 
	 */
	protected String[] getDefaultClassPaths() {
		final String [] superDefaultClassPaths = super.getDefaultClassPaths();
		final int length = superDefaultClassPaths.length;
	    String[] defaultClassPaths = new String[length + 1];
        System.arraycopy(superDefaultClassPaths, 0, defaultClassPaths, 0, length);
        defaultClassPaths[length] = path2jml4runtime;
        return defaultClassPaths;
   }

	// Augment problem detection settings
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
	    Map<String, String> options = super.getCompilerOptions();

	    options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
//	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NULLABLE);
	    options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.ENABLED);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.ERROR);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.ERROR);
	    options.put(JmlCompilerOptions.OPTION_ReportJmlCommentDisabled, CompilerOptions.ERROR);
//		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.ERROR);
//		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.ERROR);
//		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.ERROR);
		options.put(JmlCompilerOptions.OPTION_SpecPath, DbcTestCompiler.getSpecPath());
	    return options;
	}

    /*package*/ static String getSpecPath() {
		String fileSeparator = System.getProperty("file.separator"); // /
		String pathSeparator = System.getProperty("path.separator"); // :
		// String user = System.getProperty("user.name");
		// String JML2_ROOT = System.getProperty("jml2.root");
		// String JML2specs = fileSeparator + "home" + fileSeparator + user + fileSeparator + "dev" + fileSeparator + "JML2" + fileSeparator + "specs";
		String sp = "." + pathSeparator 
			+ "." + fileSeparator + "specs" + pathSeparator
			+ "." + fileSeparator + "src" + pathSeparator;
			// + JML2specs;
		return sp;
    }

    public void test_0001_requiresKeywordMissing() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ i > 0;\n" +
                "   public void m(int i) {} \n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 1)\n" +
                "	public class X {\n" +
                "	               ^\n" +
                "Syntax error on token \"{\", initially expected after this token\n" +
                "----------\n");
    }
    public void test_0002_ensuresNotSpecified() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ post \\not_specified;\n" +
                "   //@ ensures \\not_specified;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0003_ensuresSame() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ ensures \\same;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ ensures \\same;\n" +
                "	            ^^^^^\n" +
                "Syntax error on token \"\\same\", invalid Expression\n" +
                "----------\n");
    }
    public void test_0004_ensuresNothing() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ post \\nothing;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ post \\nothing;\n" +
                "	         ^^^^^^^^\n" +
                "Syntax error on token \"\\nothing\", invalid Expression\n" +
                "----------\n");
    }
    public void test_0005_requiresNotSpecified() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ pre \\not_specified;\n" +
                "   //@ requires \\not_specified;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0006_requiresSame() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ pre \\same;\n" +
                "   //@ requires \\same;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0007_requiresNothing() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ pre \\nothing;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "----------\n" +
                "1. ERROR in X.java (at line 2)\n" +
                "	//@ pre \\nothing;\n" +
                "	        ^^^^^^^^\n" +
                "Syntax error on token \"\\nothing\", invalid Expression\n" +
                "----------\n");
    }
    public void test_0008_requiresRedundantly() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ requires_redundantly true;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void _test_0008_requiresRedundantlyNotSpecified() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ requires_redundantly \\not_specified;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "FIXME: an error should be reported"); // FIXME: an error should be reported.
    }
    public void test_0009_ensuresRedundantly() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n" +
                "	/*@pure*/ int f() { return 3; }\n" +
                "   //@ ensures_redundantly 5 > this.f();\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    public void _test_0009_ensuresRedundantlyNotSpecified() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@ ensures_redundantly \\not_specified;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
        		"FIXME: an error should be reported"); // FIXME: an error should be reported.
    }
    public void test_0010_assignableRedundantly() {
        this.runConformTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   private int x;\n" +
                "   //@ assignable_redundantly x;\n" +
                "   //@ modifies_redundantly x;\n" +
                "   //@ modifiable_redundantly x;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    
    public void test_0011_oldExpression() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   int x;\n" +
                "   //@ ensures \\old(x) == x\n" +
                "   //@      && x == \\pre(x+1)-1;\n" +
                "   public void m() {} \n" +
                "}\n"
                },
                "");
    }
    
    public void test_0012_operators() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   //@   requires true ==> true;\n" +
                "   //@   requires (true ==> true);\n" +
                "   //@   requires true <== true;\n" +
                "   //@   requires (true <==> true);\n" +
                "   //@   requires false <=!=> true;\n" +
                "   //@   requires (true <==> true) ==> true;\n" +
                "   //@   requires (true <==> true) <== true;\n" +
                "   //@   requires (true <==> true) <== (true ==> (false <=!=> true));\n" +
                "   public void m() {} \n" +
                "}\n"
        },
        "");
    }
    
    public void test_0013_bug() {
		this.runNegativeTest(new String[] {
                "P.java",
                "public class P {\n"+
                "   public void m() {} \n" +
                "}\n" +
                "class C {\n"+
                "   //@ also private behavior" +
                "	//@   requires true <== true ==> true;\n" +
                "   public void m() {} \n" +
                "}\n"
		        },
				"----------\n" + 
				"1. ERROR in P.java (at line 5)\n" + 
				"	//@ also private behavior	//@   requires true <== true ==> true;\n" + 
				"	                         	                             ^^^\n" + 
				"Syntax error on token \"IMPLIES\", == expected\n" + 
				"----------\n");
    }
    
    public void test_0014_modifiers_bug() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   /*public*/ void m() {} \n" +
                "}\n" +
                "class Y extends X {\n" +
                "    /*@ also public normal_behavior\n" +
                "      @  requires true;\n" +
                "	   @  requires true <== true ==> true;\n" +
                "      @  assignable \\nothing;\n" +
                "      @  ensures true;\n" +
                "      @*/\n" +
                "   public void m() {}\n" +
                "}\n"
	        },
			"----------\n" + 
			"1. ERROR in X.java (at line 7)\n" + 
			"	@  requires true <== true ==> true;\n" + 
			"	                          ^^^\n" + 
			"Syntax error on token \"IMPLIES\", == expected\n" + 
			"----------\n");
    }
    
    public void test_0015_bugA() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n" +
                "   public /*@pure*/ X() { } \n" +
                "}\n"
	        },
			"");
    }
    
    // The following test fails if the spec path is set to the JML2 specs dir.
    public void test_0015_bugB() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n" +
                "}\n"
	        },
			"");
    }
    
    public void test_0016_jmlKeywordsAsIdentifiers() {
        this.runNegativeTest( new String[] {
                "requires.java",
                "public class requires {\n" +
                "  public requires ensures = this;\n" +
                "  //@ invariant ensures != null;\n" +
                "  //@ requires invariant != this;\n" +
                "  //@ ensures ensures == invariant;\n" +
                "  public void m(requires invariant) {\n" +
                "  }\n" +
                "}\n"
	        },
			"");
    }
    
    public void test_0017_fresh() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" + 
					"	//@ ensures \\fresh(\\result, \\result, \\result);\n" + 
					"	Object m() {return \"\";}\n" + 
					"}\n",
				},
				""
		);
    }
    
    public void test_0018_type() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" + 
					"	//@ invariant X.class == \\type(X);\n" + 
					"	//xx@ invariant \\type(int) == int.class;\n" + 
					"}\n",
				},
				""
		);
    }
    
    public void test_0019_invariant() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   //@ invariant 0;\n" +
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//@ invariant 0;\n" +
				"	              ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
    }
    
    public void test_0020_plusAt() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   //+@ invariantx 0;\n" +
					"   //+@@@ invariantx 0;\n" +
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//+@ invariantx 0;\n" +
				"	     ^^^^^^^^^^\n" +
				"Syntax error on token \"invariantx\", invariant expected\n" +
				"----------\n" +
				"2. ERROR in X.java (at line 3)\n" +
				"	//+@@@ invariantx 0;\n" +
				"	       ^^^^^^^^^^\n" +
				"Syntax error on token \"invariantx\", invariant expected\n" +
				"----------\n");
    }
    
    public void test_0021_plusAt() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   /*+@ invariant 0; */\n" +
					"   /*+@@@ invariant 0; */\n" +
					"   /*+@@@ invariant 0; @+*/\n" +
					"   /*+@@@ invariant 0; @@@+*/\n" +
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	/*+@ invariant 0; */\n" +
				"	               ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n" +
				"2. ERROR in X.java (at line 3)\n" +
				"	/*+@@@ invariant 0; */\n" +
				"	                 ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n" +
				"3. ERROR in X.java (at line 4)\n" +
				"	/*+@@@ invariant 0; @+*/\n" +
				"	                 ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n" +
				"4. ERROR in X.java (at line 5)\n" +
				"	/*+@@@ invariant 0; @@@+*/\n" +
				"	                 ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
    }
    
    public void test_0022_spaceAt() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
 					"   // @(#) ok since this is a special marker commonly used in JML2\n" +
					"   // @doclet tag ok\n" +
					"   //  @ ok, starts with two spaces\n" +
					"   // @ invariantx 0; // warn\n" +
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 5)\n" +
				"	// @ invariantx 0; // warn\n" +
				"	^^^^^\n" +
				"Possible inadvertent disabling of JML annotation\n" +
				"----------\n");
    }
    
    public void test_0023_spaceAt() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
 					"   /* @(#) ok since this is a special marker commonly used in JML2 */\n" +
					"   /* @doclet tag ok */\n" +
					"   /* @ invariantx 0; */\n" +
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 4)\n" +
				"	/* @ invariantx 0; */\n" +
				"	^^^^^\n" +
				"Possible inadvertent disabling of JML annotation\n" +
				"----------\n");
    }
    
    public void test_0024_poundAt() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   //#@ invariantx 0;\n" +
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	//#@ invariantx 0;\n" +
				"	     ^^^^^^^^^^\n" +
				"Syntax error on token \"invariantx\", invariant expected\n" +
				"----------\n");
    }
    
    public void test_0025_poundAt() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   /*#@ invariantx 0; */\n" +
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 2)\n" +
				"	/*#@ invariantx 0; */\n" +
				"	     ^^^^^^^^^^\n" +
				"Syntax error on token \"invariantx\", invariant expected\n" +
				"----------\n");
    }

	public void test_0026_leadingAt() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   /*@ \n" +
					"	  @ invariant true; */\n" +
					"   /*@ \n" +
					"	  @ invariant 0; */\n" +
					"   /*@@@ \n" +
					"	  @@@@ invariant 0; */\n" +
					"   /*+@@@ \n" +
					"	  @@@@ invariant 0; @+*/\n" +
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 5)\n" +
				"	@ invariant 0; */\n" +
				"	            ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n" +
				"2. ERROR in X.java (at line 7)\n" +
				"	@@@@ invariant 0; */\n" +
				"	               ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n" +
				"3. ERROR in X.java (at line 9)\n" +
				"	@@@@ invariant 0; @+*/\n" +
				"	               ^\n" +
				"Type mismatch: cannot convert from int to boolean\n" +
				"----------\n");
	}

	public void test_0027_atCharInMiddleOfLine() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   /*@ \n" +
					"	  @ invariant @0; */\n" +
					"}\n",
				},
				"----------\n" +
				"1. ERROR in X.java (at line 3)\n" +
				"	@ invariant @0; */\n" +
				"	            ^\n" +
				"Syntax error on token \"@\", delete this token\n" +
				"----------\n");
	}

	public void test_0028a_math_modifiers() {
		runNegativeTest(
				new String[] {
					"X.java",
					"/*@spec_java_math*/ public class X {\n" +
					"}\n" +
					"/*@code_bigint_math*/ class Y {}",
				},
				"");
	}

	public void test_0028b_misc_modifiers() {
		// Testing parser recognition of the following JML
		// declaration modifiers: ghost, helper, ...
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"	//@ ghost int gi;\n" +
					"	//@ model int i;\n" +
					"	private /*@spec_public*/ int i1;\n" +
					"	private /*@spec_protected*/ int i2;\n" +
					"   public X() { m(); }\n" +
					"   private /*@helper*/ void m() {\n" +
					"			this.i1++; this.i2++;" +
					"		}\n" +
					"}\n",
				},
				"");
	}

	public void test_0028c_modelMethod() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   /*@ requires 0 < i;\n" +
					"     @ ensures  \\result == i + i;\n" +
					"     @ public model int m(int i);\n" +
					"     @*/\n" +
					"}\n",
				},
				"");
	}
	
	public void test_0029_instance() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public interface X {\n" +
					"   //@ model instance boolean B = false;\n" +
					"}\n",
				},
				"");
	}

	public void test_0030_represents() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   //@ model boolean b;\n" +
					"   //@ represents b = true;\n" +
					"}\n",
				},
				"");
	}

	public void _test_0031_nowarn() {
		runNegativeTest(
				new String[] {
					"X.java",
					"public class X {\n" +
					"   String s = \"\".toString(); //@ nowarn NonNull;\n" +
					"}\n",
				},
				"");
	}
	
    public void test_0032_implies_that() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   /*@ normal_behavior\n" +
                "     @   requires true;\n" +
                "     @   modifies \\nothing;\n" +
                "     @ implies_that\n" +
                "     @   requires true;\n" +
                "     @*/" +
                "   public void m() {} \n" +
                "}\n"
        },
        "");
    }

    public void test_0033_void_returns_int() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                " //@ensures \\result == 0; \n" +
                "   public void m() { return 0; } \n" +
                "}\n"
        },
        "----------\n" + 
		"1. ERROR in X.java (at line 2)\n" + 
		"	//@ensures \\result == 0; \n" + 
		"	           ^^^^^^^^^^^^\n" + 
		"The operator == is undefined for the argument type(s) void, int\n" + 
		"----------\n" + 
		"2. ERROR in X.java (at line 3)\n" + 
		"	public void m() { return 0; } \n" + 
		"	                  ^^^^^^^^^\n" + 
		"Void methods cannot return a value\n" + 
		"----------\n");
    }
    
}
