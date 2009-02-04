package org.jmlspecs.eclipse.jdt.core.tests.esc.distributed;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.PostProcessor;


/*
 * 
 * PLEASE NOTE:
 * 
 * 
 * This is entirely experimental and to to be used in its current state
 * 
 * 
 * 
 * 
 * 
 */
public class ExperimentalBurdenTest extends AbstractRegressionTest{
	
	
		public ExperimentalBurdenTest(String name) {
			super(name);
		}

		@Override
		protected void setUp() throws Exception {
			super.setUp();
			PostProcessor.useOldErrorReporting = true;
		}

		@Override
		protected void tearDown() throws Exception {
			super.tearDown();
			PostProcessor.useOldErrorReporting = false;
		}

		// Augment problem detection settings
		@Override
		@SuppressWarnings("unchecked")
		protected Map<String, String> getCompilerOptions() {
			Map<String, String> options = super.getCompilerOptions();

			options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
			options.put(JmlCompilerOptions.OPTION_EnableJmlDbc, CompilerOptions.ENABLED);
			options.put(JmlCompilerOptions.OPTION_EnableJmlEsc, CompilerOptions.ENABLED);
			options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NON_NULL);
			options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.ERROR);
			options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.ERROR);
			options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
			options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.ERROR);
			options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
			options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
			options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
			// options.put(JmlCompilerOptions.OPTION_SpecPath,
			// NullTypeSystemTestCompiler.getSpecPath());
			options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.VERSION_1_5);
			options.put(CompilerOptions.OPTION_Source, CompilerOptions.VERSION_1_5);
			options.put(CompilerOptions.OPTION_TargetPlatform, CompilerOptions.VERSION_1_5);
			return options;
		}

//		private final String testsPath = "tests" + File.separatorChar + "esc" + File.separatorChar;
		// the line above fails under linux.  the following works under both linux & cygwin.
		private final String testsPath = "tests" + '\\' + "esc" + '\\';

		public void test_000_assertFalse() {
			this.runNegativeTest(new String[] {
					testsPath + "X.java",
					"package tests.esc;\n" +
					"public class X {\n" +
					"   public void m() {\n" + 
					"      //@ assert false;\n" + 
					"   }\n" + "}\n" 
					},
					"----------\n" + 
					"1. ERROR in "+testsPath+"X.java (at line 4)\n" + 
					"	//@ assert false;\n" +
					"	           ^^^^^\n" + 
					"Possible assertion failure (Assert).\n" + 
					"----------\n");
		}

		
	
		public void test_0() {
			this.runNegativeTest(new String[] {
			testsPath + "Modify.java", 
			"/** \n" +
			" ** Test escjava's reasoning about member inner classes, part III \n" +
			" **/ \n" +
			" \n" +
			" \n" +
			"/* \n" +
			" * Test modifies clauses: \n" +
			" */ \n" +
			"class Outer3 { \n" +
			"    int x; \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_1() {
			this.runNegativeTest(new String[] {
			testsPath + "Modify.java", 
			"    class Inner { \n" +
			"	Inner() {} \n" +
			" \n" +
			"	//@ modifies x \n" +
			"	Inner(int y) {} \n" +
			" \n" +
			" \n" +
			"	//@ modifies x \n" +
			"	void modify() { x = 10; } \n" +
			"    } \n" +
			" \n" +
			"    void test() { \n" +
			"	x = 3; \n" +
			"	Inner I = new Inner(); \n" +
			"	//@ assert x>0 \n" +
			"	I.modify(); \n" +
			"	//@ assert x>0         // error \n" +
			"    } \n" +
			" \n" +
			"    void test2() { \n" +
			"	x = 3; \n" +
			"	Inner I = new Inner(3); \n" +
			"	//@ assert x>0         // error \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_2() {
			this.runNegativeTest(new String[] {
			testsPath + "Post.java", 
			"/** \n" +
			" ** Test escjava's reasoning about member inner classes, part II \n" +
			" **/ \n" +
			" \n" +
			" \n" +
			"/* \n" +
			" * Verify that postconditions on enclosing instance variables work properly. \n" +
			" */ \n" +
			"class OuterPost { \n" +
			"    int x; \n" +
			" \n" +
			"    // Call from naked new: \n" +
			"    void test1() { \n" +
			"	Inner I = new Inner(); \n" +
			"	I.requireXPos(); \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Call from new with explicit instance expression: \n" +
			"    void test3() { \n" +
			"	x = 10; \n" +
			"	OuterPost o = new OuterPost(); \n" +
			" \n" +
			"	Inner I = o.new Inner(); \n" +
			"	//@ assert o.x>0 \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Verify postcondition is checked: \n" 
			}, "ERROR");
			}

			public void test_3() {
			this.runNegativeTest(new String[] {
			testsPath + "Post.java", 
			"    class Inner { \n" +
			"	//@ ensures x>0 \n" +
			"	Inner() { x=1; } \n" +
			" \n" +
			"	//@ ensures x>0 \n" +
			"	Inner(char y) {}       // error: fail because x not set \n" +
			" \n" +
			"	//@ requires x>0 \n" +
			"	void requireXPos() {} \n" +
			" \n" +
			"	//@ ensures x>0 \n" +
			"	void ensuresXPos() { x = 1; } \n" +
			" \n" +
			" \n" +
			"	// Call from a sibling constructor: \n" +
			"	//@ ensures x>0 \n" +
			"	Inner(int y) { \n" +
			"	    this(); \n" +
			"	    //@ assert x>0 \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Call via super() from a subclass... \n" 
			}, "ERROR");
			}

			public void test_4() {
			this.runNegativeTest(new String[] {
			testsPath + "Post.java", 
			"    class SubInner1 extends Inner { \n" +
			"	SubInner1(int y) { \n" +
			"	    super(); \n" +
			"	    super.requireXPos(); \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Call via E.super() from a subclass... \n" 
			}, "ERROR");
			}

			public void test_5() {
			this.runNegativeTest(new String[] {
			testsPath + "Post.java", 
			"    class SubInner2 extends Inner { \n" +
			"        //@ ensures O.x>0 \n" +
			"	SubInner2(/*@ non_null @*/ OuterPost O) { \n" +
			"	    O.super(); \n" +
			"	    //@ assert O.x>0 \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Call an instance method via an Object: \n" +
			"    void testInstance() { \n" +
			"	x = -10; \n" +
			"	Inner I = new Inner(); \n" +
			"	I.ensuresXPos(); \n" +
			"	//@ assert x>0 \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_6() {
			this.runNegativeTest(new String[] {
			testsPath + "Null.java", 
			"/** \n" +
			" ** Verify that we do null checks for the enclosing instance arguments \n" +
			" ** of new and super. \n" +
			" **/ \n" +
			" \n" +
			"class Outer { \n" 
			}, "ERROR");
			}

			public void test_7() {
			this.runNegativeTest(new String[] {
			testsPath + "Null.java", 
			"    class Inner { \n" +
			"    } \n" +
			" \n" +
			"    void test1(Outer O) { \n" +
			"	Inner I = O.new Inner();        // null error \n" +
			"    } \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_8() {
			this.runNegativeTest(new String[] {
			testsPath + "Null.java", 
			"    class Lower extends Inner { \n" +
			"	Lower(Outer O) { \n" +
			"	    O.super();                  // null error \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_9() {
			this.runNegativeTest(new String[] {
			testsPath + "Pre.java", 
			"/** \n" +
			" ** Test escjava's reasoning about member inner classes, part I \n" +
			" **/ \n" +
			" \n" +
			" \n" +
			"/* \n" +
			" * Verify that preconditions on enclosing instance variables work properly. \n" +
			" */ \n" +
			"class Outer { \n" +
			"    int x; \n" +
			" \n" +
			"    // Call from naked new: \n" +
			"    Inner test1() { \n" +
			"	return new Inner();        // error: x unknown \n" +
			"    } \n" +
			" \n" +
			"    Inner test2() { \n" +
			"	x = 10; \n" +
			"	return new Inner();        // ok \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Call from new with explicit instance expression: \n" +
			"    Inner test3() { \n" +
			"	x = 10; \n" +
			"	Outer o = new Outer(); \n" +
			" \n" +
			"	return o.new Inner();        // error: o.x unknown \n" +
			"    } \n" +
			" \n" +
			"    Inner test4() { \n" +
			"	x = -10; \n" +
			"	Outer o = new Outer(); \n" +
			"	o.x = 10; \n" +
			" \n" +
			"	return o.new Inner();        // ok \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Call from a sibling constructor: \n" 
			}, "ERROR");
			}

			public void test_10() {
			this.runNegativeTest(new String[] {
			testsPath + "Pre.java", 
			"    class Inner { \n" +
			"	//@ requires x>0 \n" +
			"	Inner() { \n" +
			"	    //@ assert x>0 \n" +
			"	} \n" +
			" \n" +
			"	//@ requires x>0 \n" +
			"	void requiresX() { \n" +
			"	    //@ assert x>0 \n" +
			"	} \n" +
			" \n" +
			" \n" +
			"	Inner(int y) { \n" +
			"	    this();           // error: x unknown \n" +
			"	} \n" +
			" \n" +
			"	//@ requires x > 10 \n" +
			"	Inner(char y) { \n" +
			"	    this();           // ok \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Call via super() from a subclass... \n" 
			}, "ERROR");
			}

			public void test_11() {
			this.runNegativeTest(new String[] {
			testsPath + "Pre.java", 
			"    class SubInner1 extends Inner { \n" +
			"	SubInner1(int y) { \n" +
			"	    super();            // error: x unknown \n" +
			"	} \n" +
			" \n" +
			"	//@ requires x>2 \n" +
			"	SubInner1(char y) { \n" +
			"	    super();            // ok \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Call via E.super() from a subclass... \n" 
			}, "ERROR");
			}

			public void test_12() {
			this.runNegativeTest(new String[] {
			testsPath + "Pre.java", 
			"    class SubInner2 extends Inner { \n" +
			"	SubInner2(/*@ non_null @*/ Outer O) { \n" +
			"	    O.super();            // error: O.x unknown \n" +
			"	} \n" +
			" \n" +
			"	//@ requires O.x>2 \n" +
			"	SubInner2(/*@ non_null @*/ Outer O, int x) { \n" +
			"	    O.super();            // ok \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // Call an instance method via an Object: \n" +
			"    void testInstance() { \n" +
			"	x = 10; \n" +
			"	Inner I = new Inner(); \n" +
			"	I.requiresX();      // no error! \n" +
			"	x = -10; \n" +
			"	I.requiresX();      // error \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_13() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures.java", 
			"/** \n" +
			" ** Test escjava's reasoning about member inner classes, part VI \n" +
			" **/ \n" +
			" \n" +
			"import java.io.IOException; \n" +
			" \n" +
			" \n" +
			"/* \n" +
			" * Verify that exsures clauses on enclosing instance variables work properly. \n" +
			" */ \n" +
			"class Outer { \n" +
			"    int x; \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_14() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures.java", 
			"    class Inner { \n" +
			"	//@ modifies x \n" +
			"	//@ ensures x<5 \n" +
			"	//@ exsures (IOException E) x>10 \n" +
			"	void m() throws IOException { x = 3; } \n" +
			"    } \n" +
			" \n" +
			"    void test() { \n" +
			"	Inner I = new Inner(); \n" +
			"	x = 6; \n" +
			"	try { \n" +
			"	    I.m(); \n" +
			"	    //@ assert x<5 \n" +
			"	} catch (IOException E) { \n" +
			"	    //@ assert x>10 \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_15() {
			this.runNegativeTest(new String[] {
			testsPath + "Deep.java", 
			"/** \n" +
			" ** Test escjava's reasoning about member inner classes, part IV \n" +
			" **/ \n" +
			" \n" +
			" \n" +
			"/* \n" +
			" * Make sure many levels of this$0 derefereces don't confuse us: \n" +
			" */ \n" +
			"class Outside { \n" +
			"    int x; \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_16() {
			this.runNegativeTest(new String[] {
			testsPath + "Deep.java", 
			"    class Level1 { \n" 
			}, "ERROR");
			}

			public void test_17() {
			this.runNegativeTest(new String[] {
			testsPath + "Deep.java", 
			"	class Level2 { \n" 
			}, "ERROR");
			}

			public void test_18() {
			this.runNegativeTest(new String[] {
			testsPath + "Deep.java", 
			"	    class Inner { \n" +
			"		//@ requires x>0 \n" +
			"		//@ modifies x \n" +
			"		//@ ensures x>5 \n" +
			"		void m() { x = 10; } \n" +
			"	    } \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    void test1() { \n" +
			"	Level1 l1 = new Level1(); \n" +
			"	Level1.Level2 l2 = l1.new Level2(); \n" +
			"	Level1.Level2.Inner I = l2.new Inner(); \n" +
			" \n" +
			"	I.m();           // error: precondition not meet \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    void test2() { \n" +
			"	Level1 l1 = new Level1(); \n" +
			"	Level1.Level2 l2 = l1.new Level2(); \n" +
			"	Level1.Level2.Inner I = l2.new Inner(); \n" +
			" \n" +
			"	x = 1; \n" +
			"	I.m(); \n" +
			"	//@ assert x>5 \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_19() {
			this.runNegativeTest(new String[] {
			testsPath + "Invariants.java", 
			"/** \n" +
			" ** Test escjava's reasoning about member inner classes, part V \n" +
			" **/ \n" +
			" \n" +
			" \n" +
			"/* \n" +
			" * Test that invariants work properly: \n" +
			" */ \n" +
			"class Outer { \n" +
			"    int x; \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_20() {
			this.runNegativeTest(new String[] {
			testsPath + "Invariants.java", 
			"    class Inner { \n" +
			"	//@ invariant Outer.this.x>0 \n" +
			" \n" +
			"	Inner() { x = 3; } \n" +
			" \n" +
			"	Inner(char y) { }    // failure to establish invariant \n" +
			" \n" +
			"	void m() { \n" +
			"	    //@ assert x>0 \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_21() {
			this.runNegativeTest(new String[] {
			testsPath + "G.java", 
			"public class G { \n" +
			" \n" +
			"  /*@non_null */public int [] a; \n" +
			"   \n" +
			"  /*@ requires a.length >= 0;  // null(a) warning \n" +
			"    @ ensures this.a == a; \n" +
			"    @*/ \n" +
			"  public G(int [] a) { \n" +
			"    this.a = a; \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires a.length == this.a.length; \n" +
			"    @ ensures this.a[i] == \\old(this.a[i]+v); \n" +
			"    @*/ \n" +
			"  public void test0(int i, int v) { \n" +
			"    this.a[i]+=v; // idxNeg(i), idx2Large(i) \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires a.length == this.a.length; \n" +
			"    @ requires i>=0 && i<this.a.length; \n" +
			"    @ ensures this.a[i] == \\old(this.a[i]+v); \n" +
			"    @*/ \n" +
			"  public void test1(int i, int v) { \n" +
			"    this.a[i]+=v; // idxNeg(i), idx2Large(i) \n" +
			"  } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_22() {
			this.runNegativeTest(new String[] {
			testsPath + "A.java", 
			"// static methods with bodies \n" +
			" \n" +
			"public class A { \n" +
			" \n" +
			"  /*@ requires i >= 0; \n" +
			"    @ ensures \\result == (i/i)*2; // divZero warning \n" +
			"    @*/ \n" +
			"  public static int test0(int i) { \n" +
			"    return 2; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i > 0; \n" +
			"    @  ensures \\result == (i/i)*2; // no divZero warning because of precondition \n" +
			"    @*/ \n" +
			"  public static int test1(int i) { \n" +
			"    return 2; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ exceptional_behavior \n" +
			"    @  requires i<0; \n" +
			"    @  signals (RuntimeException e) i<0; // null(charArray.owner) because of invariant \n" +
			"    @*/ \n" +
			"  public static int test2(int i) throws RuntimeException { \n" +
			"    throw new RuntimeException(); \n" +
			"  } \n" +
			" \n" +
			"  /*@ exceptional_behavior \n" +
			"    @  requires i<0; \n" +
			"    @  signals (RuntimeException e) i/i == i/i; // no divZero warning because of precondition \n" +
			"    @                                           // null(charArray.owner) because of invariant \n" +
			"    @*/ \n" +
			"  public static int test3(int i) throws RuntimeException { \n" +
			"    throw new RuntimeException(); \n" +
			"  } \n" +
			" \n" +
			"  /*@ exceptional_behavior \n" +
			"    @  requires i <= 0; \n" +
			"    @  signals (RuntimeException e) i/i == i/i; // divZero warning \n" +
			"    @                                           // null(charArray.owner) because of invariant \n" +
			"    @*/ \n" +
			"  public static int test4(int i) throws RuntimeException { \n" +
			"    throw new RuntimeException(); \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i>=0; \n" +
			"    @  ensures \\result == (i/i)*2; // divZero warning \n" +
			"    @ also exceptional_behavior \n" +
			"    @  requires i<0; \n" +
			"    @  signals (RuntimeException e) i/i == i/i; // no divZero because of precondition \n" +
			"    @                                           // null(charArray.owner) because of invariant \n" +
			"    @*/ \n" +
			"  public static int test5(int i) throws RuntimeException { \n" +
			"    if(i<0) \n" +
			"      throw new RuntimeException(); \n" +
			"    return 2;       \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i>0; \n" +
			"    @  ensures \\result == (i/i)*2; // no divZero warning because of precondition \n" +
			"    @ also exceptional_behavior \n" +
			"    @  requires i<=0; \n" +
			"    @  signals (RuntimeException e) i/i == i/i; // divZero warnings \n" +
			"    @                                           // null(charArray.owner) because of invariant     \n" +
			"    @*/ \n" +
			"  public static int test6(int i) throws RuntimeException { \n" +
			"    if(i<=0) \n" +
			"      throw new RuntimeException(); \n" +
			"    return (i/i)*2; \n" +
			"  } \n" +
			"	 \n" +
			"  /*@ requires i/i==i/i; // divZero warning  \n" +
			"    @*/ \n" +
			"  public static int test7(int i) { \n" +
			"    return (i/i)*2; \n" +
			"  } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_23() {
			this.runNegativeTest(new String[] {
			testsPath + "E.java", 
			"public class E { \n" +
			" \n" +
			"  //@ invariant this.f>=88;  \n" +
			"  //@ invariant f/f == f/f; // divZero warning \n" +
			"  public int f; \n" +
			" \n" +
			"  //@ invariant a.length>0; // null(a) warning \n" +
			"  public int [] a; \n" +
			" \n" +
			"  /*@ ensures \\result == this.f+1; \n" +
			"    @*/ \n" +
			"  public int test0() { \n" +
			"    return this.f+1; \n" +
			"  }  \n" +
			" \n" +
			"  /*@ requires ff>=99; \n" +
			"    @ ensures this.f == ff; \n" +
			"    @*/ \n" +
			"  public int test1(int ff) { \n" +
			"    this.f=ff; \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires ff>=99; \n" +
			"    @  requires aa.length>0; //null(aa) warning \n" +
			"    @  ensures this.f==ff; \n" +
			"    @  ensures this.a==aa; \n" +
			"    @*/ \n" +
			"  public void test2(int ff, int [] aa) { \n" +
			"    this.f=ff; \n" +
			"    this.a=aa; \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires ff>=99; \n" +
			"    @  requires aa.length>0; \n" +
			"    @  ensures this.f==ff; \n" +
			"    @  ensures this.a==aa; \n" +
			"    @*/ \n" +
			"  public void test3(int ff, /*@non_null*/int [] aa) { \n" +
			"    this.f=ff; \n" +
			"    this.a=aa; \n" +
			"  } \n" +
			" \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires ff>=99; \n" +
			"    @  requires aa.length>0; //null(aa) warning \n" +
			"    @  ensures this.f==ff; \n" +
			"    @  ensures this.a==aa; \n" +
			"    @*/ \n" +
			"  public E(int ff, int [] aa) { \n" +
			"    this.f=ff; \n" +
			"    this.a=aa; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_24() {
			this.runNegativeTest(new String[] {
			testsPath + "I.java", 
			"public class I { \n" +
			" \n" +
			"  //@ invariant this.i >= 0; \n" +
			"  public int i; \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i >= 0 && j >= 0 && k >= 0; \n" +
			"    @  ensures \\result == i+j+k; \n" +
			"    @*/ \n" +
			"  public /*@ pure */ int test0(int i, int j, int k) { \n" +
			"    return i+j+k; \n" +
			"  } \n" +
			" \n" +
			"  /*@ ensures this.i == \\old(this.test0(o1.i, o2.i, o3.i/o3.i)); \n" +
			"    @*/ \n" +
			"  public void test1(I o1, I o2, I o3) { \n" +
			"    this.i = this.test0(o1.i, o2.i, o3.i/o3.i); //null(o1),null(o2),null(o3),divZero warnings \n" +
			"  } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_25() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"// Constructors with bodies \n" +
			" \n" +
			"public class C { \n" +
			"   \n" +
			"  public int i; \n" +
			" \n" +
			"  /*@ requires i>=0; \n" +
			"    @ ensures this.i == i/i; // divZero warning \n" +
			"    @*/ \n" +
			"  public C(int i) { \n" +
			"    this.i = 1; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ requires i>=0; \n" +
			"    @ ensures this.i == i+j+k; \n" +
			"    @*/ \n" +
			"  public C(int i, int j, int k) { \n" +
			"    this.i = i+j+k; \n" +
			"  } \n" +
			" \n" +
			"  /*@ ensures this.i == o.i/o.i; // null, divZero warning \n" +
			"    @*/ \n" +
			"  public C(C o) { \n" +
			"    this.i = 1; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ requires o.i >= 0;  // null warning \n" +
			"    @ ensures this.i == o.i; // no null warning - reported in precondition \n" +
			"    @*/ \n" +
			"  public C(C o, int i) { \n" +
			"    this.i = i; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ requires o.i >= 0; // null warning \n" +
			"    @ ensures this.i == o1.i; // null warning \n" +
			"    @*/ \n" +
			"  public C(C o, C o1, int i) { \n" +
			"    this.i = i; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i >= 0; \n" +
			"    @  ensures this.i == o.i; // null warning \n" +
			"    @*/ \n" +
			"  public C(C o, int i, int j) { \n" +
			"    this.i = i; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ exceptional_behavior \n" +
			"    @  requires i >= 0; \n" +
			"    @  signals (RuntimeException e) o.i/o.i == o.i/o.i; // null(o), divZero warnings \n" +
			"    @                                                   // invariant null(charArray.owner) warning \n" +
			"    @*/ \n" +
			"  public C(C o, int i, int j, int k) throws RuntimeException { \n" +
			"    throw new RuntimeException(); \n" +
			"  } // Postcondition not established warning \n" +
			"   \n" +
			"  /*@ normal_behavior  \n" +
			"    @  requires i>=0; \n" +
			"    @  ensures this.i == o.i+o.i; // no null warnings because of body \n" +
			"    @ also exceptional_behavior \n" +
			"    @  requires i<0; \n" +
			"    @  signals (RuntimeException e) o.i/o.i == 1; // null, divZero warning \n" +
			"    @                                             // invariant null(charArray.owner) warning \n" +
			"    @*/ \n" +
			"  public C(C o, C o1, int i, int j) throws RuntimeException { \n" +
			"    if (i<0) \n" +
			"      throw new RuntimeException(); \n" +
			"    this.i = o.i+o1.i; // null (o), null (o1) warnings \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_26() {
			this.runNegativeTest(new String[] {
			testsPath + "SiblingBug.java", 
			"class SiblingBug { \n" +
			" \n" +
			"    //@ invariant x>0 \n" +
			"    int x; \n" +
			" \n" +
			"    SiblingBug() { \n" +
			"	x = 3; \n" +
			"    } \n" +
			" \n" +
			"    SiblingBug(int r) { \n" +
			"	this(); \n" +
			"    } \n" +
			" \n" +
			"    SiblingBug(char r) { \n" +
			"	this(); \n" +
			"	//@ assert x>0 \n" +
			"    } \n" +
			"   \n" +
			"    SiblingBug(boolean b) { \n" +
			"	this(); \n" +
			"	 \n" +
			"	x = x; \n" +
			" \n" +
			"	//@ assert x>0 \n" +
			"    } \n" +
			" \n" +
			"    static void m() { \n" +
			"        SiblingBug sb = new SiblingBug(); \n" +
			"	//@ assert sb.x > 0; \n" +
			"    } \n" +
			" \n" +
			"    SiblingBug(double d) { \n" +
			"        this(); \n" +
			"        x--;  // bad idea \n" +
			"    }  // invariant doesn't necessarily hold here \n" +
			" \n" +
			"    static void p() { \n" +
			"        SiblingBug sb = new SiblingBug(); \n" +
			"	sb.x = 0;  // bad idea \n" +
			"    }  // invariant doesn't necessarily hold here \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_27() {
			this.runNegativeTest(new String[] {
			testsPath + "AID.java", 
			"class AID { \n" +
			" \n" +
			"    /*@ spec_public */ byte[] theAID; \n" +
			" \n" +
			"    /*@ invariant theAID != null && \n" +
			"                  5 <= theAID.length && \n" +
			"                  theAID.length <= 16; \n" +
			"    */ \n" +
			" \n" +
			" \n" +
			"    public byte getBytes (byte[] dest, short offset) \n" +
			"    /*@ requires dest != null && dest != theAID && \n" +
			"                 offset >= 0 && \n" +
			"                 offset + theAID.length <= dest.length; \n" +
			"        modifies dest[offset .. offset+theAID.length-1]; \n" +
			"        ensures (\\forall int i; \n" +
			"                         i < offset || i >= offset + theAID.length ==> \n" +
			"                         dest[i] == \\old(dest[i])); \n" +
			"    */ \n" +
			"    { \n" +
			"      System.arraycopy(theAID, (short)0, dest, offset, (short)theAID.length); \n" +
			"      return (byte)theAID.length; \n" +
			"    } \n" +
			" \n" +
			"    public byte getBytesA (byte[] dest, short offset) \n" +
			"    /*@ requires dest != null && dest != theAID && \n" +
			"                 offset >= 0 && \n" +
			"                 offset + theAID.length <= dest.length; \n" +
			"        modifies dest[*]; \n" +
			"        ensures (\\forall int i; \n" +
			"                         i < offset || i >= offset + theAID.length ==> \n" +
			"                         dest[i] == \\old(dest[i])); \n" +
			"    */ \n" +
			"    { \n" +
			"      System.arraycopy(theAID, (short)0, dest, offset, (short)theAID.length); \n" +
			"      return (byte)theAID.length; \n" +
			"    } \n" +
			" \n" +
			"    //@ requires 5 <= len & len <= 16; \n" +
			"    public AID(int len) { \n" +
			"      theAID = new byte[len]; \n" +
			"    } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_28() {
			this.runNegativeTest(new String[] {
			testsPath + "test2.java", 
			"class test0 { \n" +
			" \n" +
			"  int sumArray(int[] a) { \n" +
			"    int s = 0; \n" +
			"    for (int i = 1; i <= a.length; i++) { \n" +
			"      s += a[i]; \n" +
			"    } \n" +
			"    return s; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_29() {
			this.runNegativeTest(new String[] {
			testsPath + "test2.java", 
			"class test1 { \n" +
			" \n" +
			"  //@ requires a != null; \n" +
			"  int sumArray(int[] a) { \n" +
			"    int s = 0; \n" +
			"    for (int i = 1; i <= a.length; i++) { \n" +
			"      s += a[i]; \n" +
			"    } \n" +
			"    return s; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_30() {
			this.runNegativeTest(new String[] {
			testsPath + "test2.java", 
			"class test2 { \n" +
			" \n" +
			"  //@ requires a != null; \n" +
			"  int sumArray(int[] a) { \n" +
			"    int s = 0; \n" +
			"    for (int i = 0; i < a.length; i++) { \n" +
			"      s += a[i]; \n" +
			"    } \n" +
			"    return s; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_31() {
			this.runNegativeTest(new String[] {
			testsPath + "OtherClass.java", 
			"class OtherClass { \n" +
			" \n" +
			"    //@ invariant x==0; \n" +
			"    int x; \n" +
			" \n" +
			"    //@ invariant y==0; \n" +
			"    static int y; \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_32() {
			this.runNegativeTest(new String[] {
			testsPath + "OtherClass.java", 
			"class OtherClassUser { \n" +
			" \n" +
			"    /* \n" +
			"     * make sure we can find an invariant in another class \n" +
			"     * via a direct field reference: \n" +
			"     */ \n" +
			" \n" +
			"    //@ requires O != null; \n" +
			"    void foo(OtherClass O) { \n" +
			"	O.x = 1; \n" +
			"    }				// error! \n" +
			" \n" +
			" \n" +
			"    //@ invariant OP != null; \n" +
			"    OtherClass OP = new OtherClass(); \n" +
			" \n" +
			"    void bar() { \n" +
			"	OP.x = 1; \n" +
			"    }				// error! \n" +
			" \n" +
			" \n" +
			"    void baz() { \n" +
			"	OtherClass.y = 1; \n" +
			"    }				// error! \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_33() {
			this.runNegativeTest(new String[] {
			testsPath + "SameClass.java", 
			"class SameClass { \n" +
			" \n" +
			"    //@ invariant x!=0; \n" +
			"    int x; \n" +
			" \n" +
			"    int y; \n" +
			" \n" +
			" \n" +
			"    // This test makes sure we know that there is an implicit reference \n" +
			"    // to x in the constructor: \n" +
			"    SameClass() { }	// error! \n" +
			" \n" +
			" \n" +
			"    void foo() { \n" +
			"	x = 0; \n" +
			"    }			// error! \n" +
			" \n" +
			"    void bar() {	// no error \n" +
			"	y = 0; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_34() {
			this.runNegativeTest(new String[] {
			testsPath + "DirectType.java", 
			"class DirectType extends Throwable {} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_35() {
			this.runNegativeTest(new String[] {
			testsPath + "DirectType.java", 
			"class DirectTypeSub extends DirectType {} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_36() {
			this.runNegativeTest(new String[] {
			testsPath + "DirectType.java", 
			"class DirectTypeSub2 extends DirectTypeSub {} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_37() {
			this.runNegativeTest(new String[] {
			testsPath + "DirectType.java", 
			"class DirectTypeUser { \n" +
			" \n" +
			"    // make sure we pull in DirectTypeSub2 <: DirectType \n" +
			" \n" +
			"    // (tests supertype closing, direct type ref...) \n" +
			"    void foo(DirectTypeSub2 x) { \n" +
			"	(DirectType)x;			// no error \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    //@ invariant ptr != null; \n" +
			"    DirectTypeSub2 ptr = new DirectTypeSub2(); \n" +
			" \n" +
			"    // similar, but instead get type from field range: \n" +
			"    void bar() { \n" +
			"	(DirectType)ptr;		// no error \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // similar, but instead get type from constructor return type: \n" +
			"    void baz() { \n" +
			"	(DirectType)(new DirectTypeSub2());		// no error \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // similar, but instead get type from new array expression: \n" +
			"    void baz2() { \n" +
			"	(DirectType[])(new DirectTypeSub2[0]);		// no error \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // similar, but instead get type from method return type: \n" +
			"    DirectTypeSub2 getit() { return new DirectTypeSub2(); } \n" +
			" \n" +
			"    void quux() { \n" +
			"	(DirectType)(getit());		// no error \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    // similar, but instead get type from method throws type: \n" +
			"    void throwit() throws DirectTypeSub2 {} \n" +
			" \n" +
			"    void beep() { \n" +
			"	try { \n" +
			"	     throwit(); \n" +
			"	} catch (DirectType x) {} \n" +
			"    }					// no (unexpected exception) error \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_38() {
			this.runNegativeTest(new String[] {
			testsPath + "Trans.java", 
			"class Trans { \n" +
			" \n" +
			"    //@ invariant x>=0; \n" +
			"    int x; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_39() {
			this.runNegativeTest(new String[] {
			testsPath + "Trans.java", 
			"class Trans2 { \n" +
			" \n" +
			"    //@ invariant ptr != null; \n" +
			"    Trans ptr = new Trans(); \n" +
			" \n" +
			"    //@ invariant y == ptr.x; \n" +
			"    int y = ptr.x; \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_40() {
			this.runNegativeTest(new String[] {
			testsPath + "Trans.java", 
			"class Trans2User { \n" +
			" \n" +
			"/* \n" +
			" * Ensure invariants are pulled in transitively when needed: \n" +
			" */ \n" +
			" \n" +
			"    //@ requires X != null; \n" +
			"    //@ ensures \\result>=0;			// no error \n" +
			"    int foo(Trans2 X) { \n" +
			"	return X.y; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_41() {
			this.runNegativeTest(new String[] {
			testsPath + "MiscFields.java", 
			"class MiscFields { \n" +
			" \n" +
			"    //@ invariant y!=0; \n" +
			"    static int y = 1; \n" +
			"} \n" +
			" \n" +
			" \n" +
			"/* \n" +
			" * Test that we see references from direct instance fields when checking \n" +
			" * constructors \n" +
			" */ \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_42() {
			this.runNegativeTest(new String[] {
			testsPath + "MiscFields.java", 
			"class MiscFieldsUser1 { \n" +
			" \n" +
			"    //@ invariant x!=0; \n" +
			"    int x = MiscFields.y; \n" +
			" \n" +
			" \n" +
			"    MiscFieldsUser1() {}		// no error \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_43() {
			this.runNegativeTest(new String[] {
			testsPath + "MiscFields.java", 
			"class MiscFieldsUser2 { \n" +
			" \n" +
			"    //@ invariant x==0; \n" +
			"    int x = MiscFields.y; \n" +
			" \n" +
			" \n" +
			"    MiscFieldsUser2() {}		// error \n" +
			"} \n" +
			" \n" +
			" \n" +
			"/* \n" +
			" * Test that we see references from referenced field specs \n" +
			" */ \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_44() {
			this.runNegativeTest(new String[] {
			testsPath + "MiscFields.java", 
			"class MiscFieldsUser3 { \n" +
			" \n" +
			"    /*@ readable_if MiscFields.y!=0; */    int x; \n" +
			" \n" +
			"    void foo() { \n" +
			"	System.out.println(x);				// no error \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_45() {
			this.runNegativeTest(new String[] {
			testsPath + "MiscFields.java", 
			"class MiscFieldsUser4 { \n" +
			" \n" +
			"    /*@ readable_if MiscFields.y==0; */    int x; \n" +
			" \n" +
			"    void foo() { \n" +
			"	System.out.println(x);				// error! \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_46() {
			this.runNegativeTest(new String[] {
			testsPath + "SuperClass.java", 
			"class SuperClass { \n" +
			" \n" +
			"    //@ invariant x!=0; \n" +
			"    int x; \n" +
			" \n" +
			"    int y; \n" +
			" \n" +
			"    SuperClass() { \n" +
			"	x = 1; \n" +
			"    } \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_47() {
			this.runNegativeTest(new String[] {
			testsPath + "SuperClass.java", 
			"class SubClass extends SuperClass { \n" +
			" \n" +
			"    SubClass() { }	// no error \n" +
			" \n" +
			" \n" +
			"    // make sure we can find an invariant in a superclass: \n" +
			"    void foo() { \n" +
			"	x = 0; \n" +
			"    }			// error! \n" +
			" \n" +
			"    void bar() {	// no error \n" +
			"	y = 0; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_48() {
			this.runNegativeTest(new String[] {
			testsPath + "MethodCall.java", 
			"class MethodCall { \n" +
			" \n" +
			"    //@ invariant x>=0; \n" +
			"    int x; \n" +
			" \n" +
			"    //@ ensures \\result==x; \n" +
			"    int getx() { return x; } \n" +
			" \n" +
			"    //@ requires arg<x; \n" +
			"    void lessx(int arg) {} \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_49() {
			this.runNegativeTest(new String[] {
			testsPath + "MethodCall.java", 
			"class MethodCallSub extends MethodCall { \n" +
			" \n" +
			"    int y; \n" +
			" \n" +
			"    //@ ensures y==x+1; \n" +
			"    MethodCallSub() { \n" +
			"	y = x+1; \n" +
			"    } \n" +
			" \n" +
			"    int getx() { return super.getx(); } \n" +
			" \n" +
			"    void lessx(int arg) {} \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_50() {
			this.runNegativeTest(new String[] {
			testsPath + "MethodCall.java", 
			"class MethodCallSubUser { \n" +
			" \n" +
			"    /* \n" +
			"     * Make sure we see references in (derived) specs of methods called \n" +
			"     */ \n" +
			" \n" +
			"    // Test ensures: \n" +
			"    //@ requires MCS != null; \n" +
			"    void foo(MethodCallSub MCS) { \n" +
			"	int z = MCS.getx(); \n" +
			"	//@ assert z>=0;			// no error \n" +
			"    } \n" +
			" \n" +
			"    // Test requires: \n" +
			"    //@ requires MCS != null; \n" +
			"    void bar(MethodCallSub MCS) { \n" +
			"	MCS.lessx(-1);			// no error \n" +
			"    } \n" +
			"    //@ requires MCS != null; \n" +
			"    void bar2(MethodCallSub MCS) { \n" +
			"	MCS.lessx(1);			// error! \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    /* \n" +
			"     * Make sure we see references in specs of constructors called via new \n" +
			"     */ \n" +
			"    void baz() { \n" +
			"	MethodCallSub mcs = new MethodCallSub(); \n" +
			" \n" +
			"	//@ assert mcs.y>=1;		// no error \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_51() {
			this.runNegativeTest(new String[] {
			testsPath + "MethodCall.java", 
			"class MethodCallSubUser1 extends MethodCallSub { \n" +
			" \n" +
			"    /* \n" +
			"     * Make sure we see references in specs of constructors called directly \n" +
			"     */ \n" +
			"    //@ ensures y>=1;			// no error \n" +
			"    MethodCallSubUser1() { \n" +
			"	this(); \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_52() {
			this.runNegativeTest(new String[] {
			testsPath + "MethodSpec.java", 
			"class MethodSpec { \n" +
			" \n" +
			"    //@ invariant x<=0; \n" +
			"    int x; \n" +
			" \n" +
			"    //@ requires arg<=x; \n" +
			"    int foo(int arg) { return 1; } \n" +
			" \n" +
			"    //@ requires arg<=x; \n" +
			"    int foo2(int arg) { return 1; } \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_53() {
			this.runNegativeTest(new String[] {
			testsPath + "MethodSpec.java", 
			"class MethodSpecSub extends MethodSpec { \n" +
			" \n" +
			"    /* \n" +
			"     * Ensure we see references in method declarations derived specs \n" +
			"     */ \n" +
			" \n" +
			"    //@ also ensures \\result<=0; \n" +
			"    int foo(int arg) { return arg; } \n" +
			" \n" +
			"    //@ also \n" +
			"    //@ requires arg <= x; \n" +
			"    //@ ensures \\result<=0; \n" +
			"    int foo2(int arg) { return arg; } \n" +
			"} \n" +
			"/* \n" +
			"Note - ESC/Java combined the specs for foo as \n" +
			"	requires arg<=x; \n" +
			"	ensures \\result <=0; \n" +
			"which could be verified. \n" +
			"ESC/Java2 combines them as \n" +
			"	requires arg<=x; \n" +
			"    also \n" +
			"	ensures \\result<=0; \n" +
			"which is \n" +
			"	requires true; \n" +
			"	ensures \\result <= 0; \n" +
			"and is not verifiable \n" +
			"*/ \n" 
			}, "ERROR");
			}

			public void test_54() {
			this.runNegativeTest(new String[] {
			testsPath + "D.java", 
			"class D { \n" +
			" \n" +
			"    static int m() \n" +
			"	//@ ensures \\result == 0; \n" +
			"	{ \n" +
			"	    return 0; \n" +
			"	} \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_55() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			" \n" +
			"    void n() { \n" +
			"	int i = D.m(); \n" +
			" \n" +
			"	//@ assert i == 0; \n" +
			" \n" +
			"	/**/ \n" +
			"	/* */ \n" +
			"	 \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_56() {
			this.runNegativeTest(new String[] {
			testsPath + "Nowarn.java", 
			"class Nowarn { \n" +
			"  void m0(int y, int x) { \n" +
			"    switch (y) { \n" +
			"      case 0: \n" +
			"	//@ decreases x; \n" +
			"	while (0 <= x) {  //@ nowarn Decreases \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 1: \n" +
			"	//@ decreases x;  //@ nowarn Decreases \n" +
			"	while (0 <= x) { \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 2: \n" +
			"	//@ decreases x; \n" +
			"	while (true) {  //@ nowarn DecreasesBound \n" +
			"	  x--; \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 3: \n" +
			"	//@ decreases x;  //@ nowarn DecreasesBound \n" +
			"	while (true) { \n" +
			"	  x--; \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 4: \n" +
			"	//@ decreases x;  // should give 2 warnings \n" +
			"	while (true) { \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 5: \n" +
			"	//@ decreases x;  // should give 1 warning \n" +
			"	while (true) {  //@ nowarn DecreasesBound \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 6: \n" +
			"	//@ decreases x;  // should give 1 warning \n" +
			"	while (true) {  //@ nowarn Decreases \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 7: \n" +
			"	//@ decreases x;  // should give 0 warnings \n" +
			"	while (true) {  //@ nowarn Decreases, DecreasesBound \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 8: \n" +
			"	//@ decreases x;  // should give 0 warnings \n" +
			"	while (true) {  //@ nowarn \n" +
			"	} \n" +
			"	break; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m1(int y, int x) { \n" +
			"    switch (y) { \n" +
			"      case 0: \n" +
			"	//@ decreases x; \n" +
			"	while (0 <= x) {  //@ nowarn \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 1: \n" +
			"	//@ decreases x;  //@ nowarn \n" +
			"	while (0 <= x) { \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 2: \n" +
			"	//@ decreases x; \n" +
			"	while (true) {  //@ nowarn \n" +
			"	  x--; \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 3: \n" +
			"	//@ decreases x;  //@ nowarn \n" +
			"	while (true) { \n" +
			"	  x--; \n" +
			"	} \n" +
			"	break; \n" +
			" \n" +
			"      case 4: \n" +
			"	//@ decreases x;  // should give 2 warnings \n" +
			"	while (true) { \n" +
			"	} \n" +
			"	break; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_57() {
			this.runNegativeTest(new String[] {
			testsPath + "E.java", 
			"class E { \n" +
			"  // This file contains some tests regarding the details of our \n" +
			"  // handling of 'decreases'. \n" +
			" \n" +
			"  void m0(int x) { \n" +
			"    // The following is fine, because of the way we check the lower bound. \n" +
			"    // Note that x may be negative on entry to the loop, but only it would \n" +
			"    // have been 0 just before the loop was evaluated. \n" +
			"    //@ decreases x; \n" +
			"    while (x-- >= 0) { } \n" +
			"    //@ assert x < -1; \n" +
			"  } \n" +
			"  void m1(int x) { \n" +
			"    // The following is also fine.  Here, x is always negative on exit \n" +
			"    // from the loop. \n" +
			"    //@ decreases x; \n" +
			"    while (x-- > 0) { } \n" +
			"    //@ assert x < 0; \n" +
			"  } \n" +
			"  void m2(int x) { \n" +
			"    //@ decreases x-1; \n" +
			"    while (x-- >= 0) { }  // variant negative \n" +
			"  } \n" +
			"  void m3(int x) { \n" +
			"    //@ decreases x-1; \n" +
			"    while (x-- > 0) { }   // variant negative \n" +
			"  } \n" +
			"  void m4(int x) { \n" +
			"    int tmp; \n" +
			"    //@ decreases x; \n" +
			"    while ((tmp = x) == (x = 1000) || true) { \n" +
			"      x = tmp-1; \n" +
			"    } \n" +
			"  } \n" +
			"  void m5(int x) { \n" +
			"    int tmp; \n" +
			"    //@ decreases x; \n" +
			"    while ((tmp = x) == (x = 1000) || true) { \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void p0(int x) { \n" +
			"    //@ decreases x; \n" +
			"    while (x > 0) { \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			"  void p1(int x) { \n" +
			"    //@ decreases x; \n" +
			"    while (true) { \n" +
			"      if (! (x > 0)) { \n" +
			"	break; \n" +
			"      } \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			"  void p2(int x) { \n" +
			"    //@ decreases j; \n" +
			"    for (int j = x; j > 0; j--) { \n" +
			"    } \n" +
			"  } \n" +
			"  void p3(int x) { \n" +
			"    //@ decreases x; \n" +
			"    do { \n" +
			"    } while (x-- >= 0); \n" +
			"  } \n" +
			"  void p4(int x) { \n" +
			"    //@ decreases x; \n" +
			"    while (true) { } \n" +
			"  } \n" +
			"  void p5(int x) { \n" +
			"    //@ decreases x; \n" +
			"    for ( ; ; ) { } \n" +
			"  } \n" +
			"  void p6(int x) { \n" +
			"    //@ decreases x; \n" +
			"    do { } while (true); \n" +
			"  } \n" +
			" \n" +
			"  void q0(int x) { \n" +
			"    //@ decreases x; \n" +
			"    while (0 <= x) {  // does not necessarily decrease variant function \n" +
			"      if (x % 13 < 7) { \n" +
			"	x--; \n" +
			"      } else if (x / 34 == 5) { \n" +
			"	x += 2; \n" +
			"      } \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			"  void q1(int x) { \n" +
			"    //@ decreases x;   // not decreased, and \n" +
			"    while (-2 <= x) {  // negative variant function does not lead to exit \n" +
			"      if (x == -2) { \n" +
			"	break; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			"  void q2(int x) { \n" +
			"    //@ decreases x; \n" +
			"    while (-2 <= x) {  // does not decrease variant function \n" +
			"      if (x == -2) { \n" +
			"	break; \n" +
			"      } \n" +
			"      x++; \n" +
			"      if (x == 0) { \n" +
			"	break; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			"  void q3(int x) { \n" +
			"    //@ decreases x; \n" +
			"    while (-2 <= x) { \n" +
			"      if (x == -2) { \n" +
			"	break; \n" +
			"      } \n" +
			"      x -= 5; \n" +
			"      if (x == -6) { \n" +
			"	break; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 95 <= z; \n" +
			"  void r0(int x, int z, boolean b) { \n" +
			"    //@ decreases t; \n" +
			"    //@ loop_invariant 95 <= t; \n" +
			"    for (int t = z; t != 95; t--) { \n" +
			"      r1(x); \n" +
			"      r1(x+1); \n" +
			"      //@ assert b;  // just to check we get here \n" +
			"    } \n" +
			"  } \n" +
			"  //@ helper \n" +
			"  final void r1(int y) { \n" +
			"    //@ decreases y; \n" +
			"    while (y > 0) { \n" +
			"      y--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void s0(int x, int y) { \n" +
			"    //@ decreases x; \n" +
			"    //@ decreases y; \n" +
			"    while (true) { \n" +
			"      if (x < 0 || y < 0) { \n" +
			"	break; \n" +
			"      } \n" +
			"      x--; \n" +
			"      y--; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_58() {
			this.runNegativeTest(new String[] {
			testsPath + "F.java", 
			"class F { \n" +
			"  void bound0(int x) {  // always okay \n" +
			"    //@ decreases x; \n" +
			"    while (0 <= x) { \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void bound1(int x) {  // bound error always detected \n" +
			"    //@ decreases x; \n" +
			"    while (true) { \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 0 <= x; \n" +
			"  void bound2(int x) {  // bound error detected with 2 or more unrollings \n" +
			"    //@ decreases x; \n" +
			"    while (true) { \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 3 <= x; \n" +
			"  void bound3(int x) {  // bound error detected with 5 or more unrollings \n" +
			"    //@ decreases x; \n" +
			"    while (true) { \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 4 <= x; \n" +
			"  void bound4(int x) {  // bound error detected with 6 or more unrollings \n" +
			"    //@ decreases x; \n" +
			"    while (true) { \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void bound5(int x) {  // no bound error, unbeknownst to loopSafe \n" +
			"    boolean b = false; \n" +
			"    //@ decreases x; \n" +
			"    while (x != 0) { \n" +
			"      if (!b && x < 10) { \n" +
			"	break; \n" +
			"      } \n" +
			"      b = true; \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void bound6(int x) {  // no bound error, and loopSafe knows it \n" +
			"    boolean b = false; \n" +
			"    //@ loop_invariant b ==> 0 <= x; \n" +
			"    //@ decreases x; \n" +
			"    while (x != 0) { \n" +
			"      if (!b && x < 10) { \n" +
			"	break; \n" +
			"      } \n" +
			"      b = true; \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void decr0(int x) {  // always decreases \n" +
			"    //@ decreases x; \n" +
			"    while (0 <= x) { \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void decr1(int x) {  // decrease error always detected \n" +
			"    //@ decreases x; \n" +
			"    while (0 <= x) { \n" +
			"      if (x != 0) { \n" +
			"	x--; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 1 <= x; \n" +
			"  void decr2(int x) {  // decrease error detected with 2 or more iterations \n" +
			"    //@ decreases x; \n" +
			"    while (0 <= x) { \n" +
			"      if (x != 0) { \n" +
			"	x--; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 4 <= x; \n" +
			"  void decr3(int x) {  // decrease error detected with 5 or more iterations \n" +
			"    //@ decreases x; \n" +
			"    while (0 <= x) { \n" +
			"      if (x != 0) { \n" +
			"	x--; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 6 <= x; \n" +
			"  void decr4(int x) {  // decrease error detected with 6 or more iterations \n" +
			"    //@ decreases x; \n" +
			"    while (0 <= x) { \n" +
			"      if (x != 0) { \n" +
			"	x--; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void decr5(int x) {  // no decrease error, unbeknownst to loopSafe \n" +
			"    boolean b = false; \n" +
			"    //@ decreases x; \n" +
			"    while (0 <= x) { \n" +
			"      if (b) { \n" +
			"	x = 80; \n" +
			"	b = false; \n" +
			"      } else if (!b && 100 <= x) { \n" +
			"	b = true; \n" +
			"      } \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void decr6(int x) {  // no decrease error and loopSafe knows it \n" +
			"    boolean b = false; \n" +
			"    //@ loop_invariant b ==> 99 <= x; \n" +
			"    //@ decreases x; \n" +
			"    while (0 <= x) { \n" +
			"      if (b) { \n" +
			"	x = 80; \n" +
			"	b = false; \n" +
			"      } else if (!b && 100 <= x) { \n" +
			"	b = true; \n" +
			"      } \n" +
			"      x--; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_59() {
			this.runNegativeTest(new String[] {
			testsPath + "D.java", 
			"class D { \n" +
			"  void p0() { \n" +
			"    int x = 5; \n" +
			"    while (true) { \n" +
			"      //@ decreases x;   // wrong placement \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m0() { \n" +
			"    //@ decreases x;   // undefined variable \n" +
			"    while (true) { \n" +
			"      int x = 5; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m1() { \n" +
			"    //@ decreases x;   // undefined variable \n" +
			"    do { \n" +
			"      int x = 5; \n" +
			"    } while (true); \n" +
			"  } \n" +
			" \n" +
			"  void m2() { \n" +
			"    //@ decreases x;   // undefined variable \n" +
			"    for (int t = 0; t < 10; t++) { \n" +
			"      int x = t; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_60() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			"  void m0(int x) { \n" +
			"    //@ decreases 10-x; \n" +
			"    while (x < 10) { \n" +
			"      x++; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m1(int x) { \n" +
			"    //@ decreases 10-x; \n" +
			"    do { \n" +
			"      x++; \n" +
			"    } while (x < 10); \n" +
			"  } \n" +
			" \n" +
			"  void m2(int t) { \n" +
			"    //@ decreases 10-x; \n" +
			"    for (int x = t; x < 10; x++) { \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x <= 10; \n" +
			"  void m3(int x) { \n" +
			"    //@ decreases 10-x; \n" +
			"    //@ loop_invariant x <= 10; \n" +
			"    //@ decreases 100-x; \n" +
			"    //@ decreases 84-x; \n" +
			"    while (x < 10) { \n" +
			"      x++; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void p0(int x) { \n" +
			"    //@ decreases 9-x; \n" +
			"    while (x < 10) { \n" +
			"      x++; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void p1(int x) { \n" +
			"    //@ decreases 9-x; \n" +
			"    do { \n" +
			"      x++; \n" +
			"    } while (x < 10); \n" +
			"  } \n" +
			" \n" +
			"  void p2(int t) { \n" +
			"    //@ decreases 9-x; \n" +
			"    for (int x = t; x < 10; x++) { \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x <= 10; \n" +
			"  void p3(int x) { \n" +
			"    //@ loop_invariant x <= 10; \n" +
			"    //@ decreases 99-x; \n" +
			"    //@ decreases 9-x; \n" +
			"    //@ decreases 83-x; \n" +
			"    while (x < 10) { \n" +
			"      x++; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void q0(int x) { \n" +
			"    //@ decreases 8-x;  // variant negative \n" +
			"    while (x < 10) { \n" +
			"      x++; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void q1(int x) { \n" +
			"    //@ decreases 8-x; \n" +
			"    do { \n" +
			"      x++; \n" +
			"    } while (x < 10); \n" +
			"  } \n" +
			" \n" +
			"  void q2(int t) { \n" +
			"    //@ decreases 8-x;  // variant negative \n" +
			"    for (int x = t; x < 10; x++) { \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x <= 10; \n" +
			"  void q3(int x) { \n" +
			"    //@ loop_invariant x <= 10; \n" +
			"    //@ decreases 98-x; \n" +
			"    //@ decreases 8-x;  // variant negative \n" +
			"    //@ decreases 82-x; \n" +
			"    while (x < 10) { \n" +
			"      x++; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void r0(int x) { \n" +
			"    //@ decreases 7-x;  // variant negative \n" +
			"    while (x < 10) { \n" +
			"      x++; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void r1(int x) { \n" +
			"    //@ decreases 7-x;  // variant negative \n" +
			"    do { \n" +
			"      x++; \n" +
			"    } while (x < 10); \n" +
			"  } \n" +
			" \n" +
			"  void r2(int t) { \n" +
			"    //@ decreases 7-x;  // variant negative \n" +
			"    for (int x = t; x < 10; x++) { \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x <= 10; \n" +
			"  void r3(int x) { \n" +
			"    //@ loop_invariant x <= 10; \n" +
			"    //@ decreases 97-x; \n" +
			"    //@ decreases 7-x;  // variant negative \n" +
			"    //@ decreases 81-x; \n" +
			"    while (x < 10) { \n" +
			"      x++; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_61() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"// tests final class axiom and distinct types axiom \n" +
			"import java.io.IOException; \n" +
			" \n" +
			"public class C { \n" +
			"    public static void test1() throws IOException { \n" +
			"	String s; \n" +
			"	//	throw new IOException();  \n" +
			"	return; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_62() {
			this.runNegativeTest(new String[] {
			testsPath + "SynchHotspot.java", 
			"/** This test file produces various sychronization warnings to make sure that \n" +
			" ** the caret positions in the error messages are placed correctly.<p> \n" +
			" ** \n" +
			" ** This file does not check any non-synchronization errors.  These are \n" +
			" ** found in file Hotspot.java. \n" +
			" **/ \n" +
			" \n" +
			"class SynchHotspot { \n" +
			"  //@ monitored \n" +
			"  int x; \n" +
			" \n" +
			"  Object mu0, mu1; \n" +
			"  double[] d /*@ monitored_by mu0, this.mu1; */; \n" +
			" \n" +
			"  SynchHotspot() { \n" +
			"    // These don't give any warnings in constructors \n" +
			"    x = 0; \n" +
			"    d = null; \n" +
			"  } \n" +
			"   \n" +
			"  int mRace0() { \n" +
			"    return x; \n" +
			"  } \n" +
			"   \n" +
			"  int mRace1() { \n" +
			"    return this.x; \n" +
			"  } \n" +
			"   \n" +
			"  void mRace2() { \n" +
			"    x = 5; \n" +
			"  } \n" +
			"   \n" +
			"  void mRace3() { \n" +
			"    this.x = 5; \n" +
			"  } \n" +
			"   \n" +
			"  void mRace4() { \n" +
			"    this.x += 5; \n" +
			"  } \n" +
			"   \n" +
			"  void mRace5() { \n" +
			"    this.x++; \n" +
			"  } \n" +
			"   \n" +
			"  void mRace6() { \n" +
			"    ++this.x; \n" +
			"  } \n" +
			"   \n" +
			"  double[] mRace7() { \n" +
			"    return d; \n" +
			"  } \n" +
			"   \n" +
			"  void mRace8() { \n" +
			"    d = new double[100]; \n" +
			"  } \n" +
			" \n" +
			"  double mRace9() { \n" +
			"    return d[1]; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires d != null; \n" +
			"  void mRace10() { \n" +
			"    this.d[0] = 0.1e2; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this || \\lockset[this]; \n" +
			"  synchronized void mRace11() { \n" +
			"    x++;  // okay \n" +
			"    d = null;  // not okay \n" +
			"  } \n" +
			" \n" +
			"  //@ requires mu0 != null && \\max(\\lockset) < mu0; \n" +
			"  void mRace12() { \n" +
			"    double[] a; \n" +
			"    synchronized (mu0) { \n" +
			"      a = d;  // okay \n" +
			"    } \n" +
			"    double y; \n" +
			"    if (a != null && a.length != 0) { \n" +
			"      y = a[0];  // okay, even though this gets the element d[0]  (we don't \n" +
			"                 // have an annotation to prevent this) \n" +
			"    } \n" +
			"    synchronized (mu0) { \n" +
			"      d = null;  // race condition (mu1 is not held) \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires mu0 != null && mu1 != null; \n" +
			"  //@ requires \\max(\\lockset) < mu0 && mu0 < mu1; \n" +
			"  void mRace13() { \n" +
			"    double[] a; \n" +
			"    synchronized (mu0) { \n" +
			"      a = d;  // okay \n" +
			"    } \n" +
			"    synchronized (mu1) { \n" +
			"      a = d;  // okay \n" +
			"    } \n" +
			"    synchronized (mu0) { \n" +
			"      synchronized (mu1) { \n" +
			"	a = d;  // okay \n" +
			"	d = a;  // okay \n" +
			"      } \n" +
			"    } \n" +
			"    synchronized (mu1) { \n" +
			"      d = a;  // race condition (mu0 not held) \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires mu1 != null && \\max(\\lockset) < mu1; \n" +
			"  void mRace14() { \n" +
			"    double[] a = d;  // okay \n" +
			"    d = a;  // race condition (mu0 not held) \n" +
			"  } \n" +
			" \n" +
			"  synchronized int mRace15(SynchHotspot h) { //@ nowarn Deadlock; \n" +
			"    int y = x;  // okay \n" +
			"    if (h == null) { \n" +
			"      return 0; \n" +
			"    } else { \n" +
			"      return y + h.x;  // race condition (h not held) \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void mDeadlock0() { \n" +
			"    synchronized (mu0) {  // trying to lock null \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this || \\lockset[this]; \n" +
			"  synchronized void mDeadlock1() { \n" +
			"    synchronized (this) { // okay \n" +
			"      synchronized (this) { // okay \n" +
			"	if (mu0 != null) { \n" +
			"	  synchronized (mu0) {  // possible deadlock \n" +
			"	  } \n" +
			"	} \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void mDeadlock2() { \n" +
			"    mDeadlock1();  // does not respect locking order \n" +
			"  } \n" +
			" \n" +
			"  void mDeadlock3() { \n" +
			"    this.mDeadlock1();  // does not respect locking order \n" +
			"  } \n" +
			" \n" +
			"  void mDeadlock4(SynchHotspot h) { \n" +
			"    if (h != null) { \n" +
			"      h.mDeadlock1();  // does not respect locking order \n" +
			"    } \n" +
			"  } \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_63() {
			this.runNegativeTest(new String[] {
			testsPath + "SynchHotspot.java", 
			"  //@ requires \\max(\\lockset) < SynchHotspot.class || \\lockset[SynchHotspot.class]; \n" +
			"  static synchronized void mDeadlock5(SynchHotspot h) { \n" +
			"    if (h == null) { \n" +
			"      mDeadlock5(h); \n" +
			"    } else { \n" +
			"      h.mDeadlock1();  // does not respect locking order \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  static void mDeadlock6() { \n" +
			"    mDeadlock5(null);  // does not respect locking order \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_64() {
			this.runNegativeTest(new String[] {
			testsPath + "Hotspot.java", 
			"/** This test file produces various warnings to make sure that \n" +
			" ** the caret positions in the error messages are placed correctly.<p> \n" +
			" ** \n" +
			" ** This file does not check any synchronization errors.  These are \n" +
			" ** found in file SynchHotspot.java. \n" +
			" **/ \n" +
			" \n" +
			"class HotspotSuper { \n" +
			"  static int gg;  //@ invariant 0 <= gg; \n" +
			" \n" +
			"  //@ requires gg != 4; \n" +
			"  HotspotSuper() { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 0 < z; \n" +
			"  HotspotSuper(int z) { \n" +
			"    gg = z; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_65() {
			this.runNegativeTest(new String[] {
			testsPath + "Hotspot.java", 
			"public class Hotspot extends HotspotSuper { \n" +
			"  int ff; \n" +
			"  float flfl; \n" +
			"  double dodo; \n" +
			"  Object nn /*@ non_null */; \n" +
			"  int kk = 6;  /*@ invariant kk == kk;  invariant 0 <= kk; */ \n" +
			" \n" +
			"  int uuCount /*@ readable_if uuArray != null; */; \n" +
			"  int[] uuArray; \n" +
			"	     \n" +
			"  // The following constructor contains no errors \n" +
			"  Hotspot(int x) /*@ requires 10 <= x && gg != 4; \n" +
			"		     ensures kk == 6; ensures ff == 0; */ { \n" +
			"    nn = this; \n" +
			"  } \n" +
			" \n" +
			"  int mNullField0(Hotspot h) { \n" +
			"    return h.ff; \n" +
			"  } \n" +
			" \n" +
			"  void mNullField1(Hotspot h) { \n" +
			"    h.ff = 2; \n" +
			"  } \n" +
			" \n" +
			"  void mNullField2(Hotspot h) { \n" +
			"    h.ff += 2; \n" +
			"  } \n" +
			" \n" +
			"  void mNullField3(Hotspot h) { \n" +
			"    h.ff++; \n" +
			"  } \n" +
			" \n" +
			"  void mNullField4(Hotspot h) { \n" +
			"    ++h.ff; \n" +
			"  } \n" +
			" \n" +
			"  int mNullField5(int a[]) { \n" +
			"    return a.length; \n" +
			"  } \n" +
			" \n" +
			"  int mNullArray0(int a[]) { \n" +
			"    return a[0]; \n" +
			"  } \n" +
			"   \n" +
			"  void mNullArray1(int a[]) { \n" +
			"    a[0] = 8; \n" +
			"  } \n" +
			"   \n" +
			"  void mNullArray2(int a[]) { \n" +
			"    a[0] += 8; \n" +
			"  } \n" +
			"   \n" +
			"  void mNullArray3(int a[]) { \n" +
			"    a[0]++; \n" +
			"  } \n" +
			"   \n" +
			"  void mNullArray4(int a[]) { \n" +
			"    ++a[0]; \n" +
			"  } \n" +
			" \n" +
			"  void mNullCall(Hotspot h) { \n" +
			"    h.mNullCall(h); \n" +
			"  } \n" +
			"   \n" +
			"  void mNullThrow0(Hotspot h) throws Throwable { \n" +
			"    Throwable e = null; \n" +
			"    throw e; \n" +
			"  } \n" +
			" \n" +
			"  void mNullThrow1(Hotspot h) throws Throwable { \n" +
			"    Throwable e = null; \n" +
			"    Label: throw e; \n" +
			"  } \n" +
			" \n" +
			"  void NullSynchronized(Object mu) { \n" +
			"    synchronized (mu) { \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  int mBoundsBelow(int a[], int n) { \n" +
			"    if (a != null) { \n" +
			"      return a[n]; \n" +
			"    } else { \n" +
			"      return 0; \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  int mBoundsAbove(int a[], int n) { \n" +
			"    if (a != null && 0 <= n) { \n" +
			"      return a[n]; \n" +
			"    } else { \n" +
			"      return 0; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  int mZeroDiv0(int x, int y, float f, double d) { \n" +
			"    f = f / f;  // okay \n" +
			"    d = d / d;  // okay \n" +
			"    return x / y; \n" +
			"  } \n" +
			" \n" +
			"  void mZeroDiv1(int x, int y, float f, double d) { \n" +
			"    f /= f;  // okay \n" +
			"    d /= d;  // okay \n" +
			"    x /= y; \n" +
			"  } \n" +
			" \n" +
			"  void mZeroDiv2(int y, float f, double d) { \n" +
			"    flfl /= f;  // okay \n" +
			"    dodo /= d;  // okay \n" +
			"    ff /= y; \n" +
			"  } \n" +
			" \n" +
			"  void mZeroDiv3(int[] ai, float[] af, double[] ad) { \n" +
			"    if (af != null && af.length != 0) { \n" +
			"      af[0] /= af[0];  // okay \n" +
			"    } \n" +
			"    if (ad != null && ad.length != 0) { \n" +
			"      ad[0] /= ad[0];  // okay \n" +
			"    } \n" +
			"    if (ai != null && ai.length != 0) { \n" +
			"      ai[0] /= ai[0]; \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  int mZeroMod0(int x, int y, float f, double d) { \n" +
			"    f = f % f;  // okay \n" +
			"    d = d % d;  // okay \n" +
			"    return x % y; \n" +
			"  } \n" +
			" \n" +
			"  void mZeroMod1(int x, int y, float f, double d) { \n" +
			"    f %= f; \n" +
			"    d %= d; \n" +
			"    x %= y; \n" +
			"  } \n" +
			" \n" +
			"  void mZeroMod2(int y, float f, double d) { \n" +
			"    flfl %= f;  // okay \n" +
			"    dodo %= d;  // okay \n" +
			"    ff %= y; \n" +
			"  } \n" +
			" \n" +
			"  void mZeroMod3(int[] ai, float[] af, double[] ad) { \n" +
			"    if (af != null && af.length != 0) { \n" +
			"      af[0] %= af[0];  // okay \n" +
			"    } \n" +
			"    if (ad != null && ad.length != 0) { \n" +
			"      ad[0] %= ad[0];  // okay \n" +
			"    } \n" +
			"    if (ai != null && ai.length != 0) { \n" +
			"      ai[0] %= ai[0]; \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  Hotspot mCast(Object o) { \n" +
			"    return (Hotspot)o; \n" +
			"  } \n" +
			" \n" +
			"  void mNonNullVar0(Object o) { \n" +
			"    /*@ non_null */ Object x; \n" +
			"    x = o; \n" +
			"  } \n" +
			"   \n" +
			"  void mNonNullVar1(Object o) { \n" +
			"    /*@ non_null */ Object x = o; \n" +
			"  } \n" +
			"   \n" +
			"  void mNonNullField(Object o) { \n" +
			"    nn = o; \n" +
			"  } \n" +
			"   \n" +
			"  void mNonNullParam(Object o, /*@ non_null */ Object p) { \n" +
			"    /*@ non_null */ Object x = p; \n" +
			"    mNonNullParam(o, x);  // this is okay \n" +
			"    mNonNullParam(o, (5 < 2 ? p : o));  // this is not \n" +
			"  } \n" +
			" \n" +
			"  void mArrayStore(Object[] a) { \n" +
			"    if (a != null && a.length == 12) { \n" +
			"      a[7] = this; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void mAssert(int x) { \n" +
			"    //@ assert x < 2; \n" +
			"  } \n" +
			"   \n" +
			"  void mUnreachable(int x) { \n" +
			"    if (x != 2) { \n" +
			"      switch (x) { \n" +
			"	case 0:  break; \n" +
			"	case 1: \n" +
			"	case 2: \n" +
			"	  //@ unreachable; \n" +
			"	  break; \n" +
			"	default: \n" +
			"	  break; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x != 0; \n" +
			"  void mPreRequires0(int x) { \n" +
			"    mPreRequires0(  x -1 ); \n" +
			"  } \n" +
			"   \n" +
			"  //@ requires x != 0; \n" +
			"  void mPreRequires1(int x) { \n" +
			"    this.mPreRequires1(x-1); \n" +
			"  } \n" +
			"   \n" +
			"  //@ requires h != null && x != 0; \n" +
			"  void mPreRequires2(Hotspot h, int x) { \n" +
			"    h.mPreRequires2(this, x-1); \n" +
			"  } \n" +
			"   \n" +
			"  //@ requires x != 0; \n" +
			"  static void mPreRequires3(int x) { \n" +
			"    mPreRequires3(x-1); \n" +
			"  } \n" +
			" \n" +
			"  void mPreRequires4(int x) { \n" +
			"    Hotspot h = new Hotspot(x); \n" +
			"  } \n" +
			" \n" +
			"  Hotspot(Hotspot hnn) { \n" +
			"    super(-5);  // fails to meet HotspotSuper(int) precondition \n" +
			"    if (hnn != null) { \n" +
			"      nn = hnn; \n" +
			"    } else { \n" +
			"      nn = this; \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  Hotspot(int x, int y) { \n" +
			"    this(x+y);  // fails to meet Hotspot(int) precondition \n" +
			"  } \n" +
			" \n" +
			"  Hotspot(double d) {  // fails to meet HotspotSuper() precondition \n" +
			"  } \n" +
			" \n" +
			"  void mPreInvariant0() { \n" +
			"    gg = -2; \n" +
			"    mPreInvariant0(); \n" +
			"  } \n" +
			"   \n" +
			"  void mPreInvariant1() { \n" +
			"    gg = -2; \n" +
			"    this.mPreInvariant1(); \n" +
			"  } \n" +
			"   \n" +
			"  void mPreInvariant2(Hotspot h) { \n" +
			"    gg = -2; \n" +
			"    if (h != null) { \n" +
			"      h.mPreInvariant2(this); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void mPreInvariant3() { \n" +
			"    gg = -8; \n" +
			"    Hotspot h = new Hotspot(12, 14); \n" +
			"  } \n" +
			" \n" +
			"  Hotspot(float f, double d) { \n" +
			"    super(- (gg= -3)); // meets HotspotSuper(int) precondition, but violates \n" +
			"                       // an invariant \n" +
			"  } \n" +
			" \n" +
			"  Hotspot(float f0, float f1, float f2) { \n" +
			"    this((float)(gg= -3), f1);  // meets Hotspot(float, double) precondition, but \n" +
			"                                // violates an invariant \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires x < 0; ensures \\result == 12; */ \n" +
			"  int mPostEnsures0(int x) { \n" +
			"    return x; \n" +
			"  } \n" +
			"   \n" +
			"  /*@ ensures ff == 12; */ \n" +
			"  void mPostEnsures1(int x) { \n" +
			"    ff = x; \n" +
			"  } \n" +
			" \n" +
			"  /*@ exsures (SomeException se) se == null; */ \n" +
			"  void mPostExsures0() throws Throwable { \n" +
			"    throw new SomeException(); \n" +
			"  } \n" +
			"   \n" +
			"  //@ ensures kk == 0; \n" +
			"  Hotspot(int[] a) { \n" +
			"    super(12); \n" +
			"    nn = this; \n" +
			"  } \n" +
			" \n" +
			"  // Conspicuously missing from this test file are methods that violate \n" +
			"  // modifies clauses, but our checker doesn't currently support modifies \n" +
			"  // checking. \n" +
			"   \n" +
			"  void mPostInvariant0(int x) { \n" +
			"    gg = x; \n" +
			"  } \n" +
			" \n" +
			"  void mPostInvariant1(int x) { \n" +
			"    kk = x; \n" +
			"  } \n" +
			" \n" +
			"  Hotspot(double[][] aad) { \n" +
			"    this((int[])null); \n" +
			"    if (aad != null && 15 < aad.length && aad[10] != null && aad[10].length != 0) { \n" +
			"      kk = (int)aad[10][0];  // may fail to establish invariant \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  Hotspot(double[][] aad, int x) { \n" +
			"    this((int[])null); \n" +
			"    gg = x;  // may fail to establish invariant \n" +
			"  } \n" +
			" \n" +
			"  void mPostException0(RuntimeException e) { \n" +
			"    if (e != null) { \n" +
			"      throw e; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void mPostException1(RuntimeException e) { \n" +
			"    if (e != null) { \n" +
			"      Label: throw e; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void mUninit0() { \n" +
			"    int x = 13 /*@ uninitialized */; \n" +
			"    int y = 2; \n" +
			"    if (x < y) { \n" +
			"      y++; \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  void mUninit1(int z, int w) { \n" +
			"    int x = 0 /*@ uninitialized */; \n" +
			"    int y = 0 /*@ uninitialized */; \n" +
			"    if (z == 10) { \n" +
			"      y = 68; \n" +
			"    } else { \n" +
			"      y = 72; \n" +
			"    } \n" +
			"    if (y < 70) {  // okay \n" +
			"      x = 20; \n" +
			"    } \n" +
			"    if (z == 10 && x < w) {  // okay \n" +
			"      y++; \n" +
			"    } \n" +
			"    x++;  // possible read of meaningless value \n" +
			"  } \n" +
			" \n" +
			"  int mUndef0(int[] a) { \n" +
			"    /*@ readable_if a != null; */ int c; \n" +
			"    c = 12;    // always okay to write to c \n" +
			"    return c;  // but can read c only if a is non-null \n" +
			"  } \n" +
			" \n" +
			"  int mUnwrit0(int[] a) { \n" +
			"    /*@ writable_if a != null; */ int c; \n" +
			" \n" +
			"    if (a==null) \n" +
			"	c = 3;    // error: not ok to write to c if a==null \n" +
			"    else \n" +
			"	c = 12;    // ok here \n" +
			"    return c;  // but can read c always \n" +
			"  } \n" +
			"   \n" +
			"  int mUndef1(int[] a, int[] b) { \n" +
			"    /*@ readable_if a != null; */ int c = 12; \n" +
			"    if (a != null) { \n" +
			"      return c; \n" +
			"    } \n" +
			"    a = new int[3]; \n" +
			"    int z = c;   // okay, since a is now non-null \n" +
			"    c = a[2]; \n" +
			"    a = b; \n" +
			"    return z + c; \n" +
			"  } \n" +
			"   \n" +
			"  int mUndef2() { \n" +
			"    uuCount = 12;    // always okay to write to uuCount \n" +
			"    return uuCount;  // but can read uuCount only if uuArray is non-null \n" +
			"  } \n" +
			" \n" +
			"  void mUndef3() { \n" +
			"    int[] a = new int[10] //@ readable_if gg < 10; \n" +
			"      ; \n" +
			"    if (gg == 7) { \n" +
			"      a[0] += 1;  // okay \n" +
			"    } \n" +
			"    a[1] *= 20;  // not okay \n" +
			"  } \n" +
			" \n" +
			"  int mUndef4() { \n" +
			"    boolean b; \n" +
			"    int c /*@ readable_if b; */; \n" +
			"    b = false; \n" +
			"    c = 0; \n" +
			"    return c; \n" +
			"  } \n" +
			" \n" +
			"  /***************** \n" +
			"  void mUndef5() { \n" +
			"    //@ readable_if 0 <= c; \n" +
			"    int c = 6; \n" +
			"    c++;  // okay \n" +
			"    c -= 8;  // okay \n" +
			"    c++;  // not okay \n" +
			"  } \n" +
			"  *****************/ \n" +
			" \n" +
			"  void mLoopInvInitWhile() { \n" +
			"    int x = 0; \n" +
			"    //@ loop_invariant x != 0; \n" +
			"    while (true) { \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void mLoopInvIterWhile() { \n" +
			"    int x = 1; \n" +
			"    //@ loop_invariant x != 0; \n" +
			"    while (true) { \n" +
			"      x = 0; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void mLoopInvInitDo0() { \n" +
			"    int x = 0; \n" +
			"    //@ loop_invariant x != 0; \n" +
			"    do { \n" +
			"    } while (true); \n" +
			"  } \n" +
			" \n" +
			"  void mLoopInvInitDo1() { \n" +
			"    int x = 0; \n" +
			"    //@ loop_invariant x != 0; \n" +
			"    Label: do { \n" +
			"    } while (true); \n" +
			"  } \n" +
			" \n" +
			"  void mLoopInvIterDo0() { \n" +
			"    int x = 1; \n" +
			"    //@ loop_invariant x != 0; \n" +
			"    do { \n" +
			"      x = 0; \n" +
			"    } while (true); \n" +
			"  } \n" +
			" \n" +
			"  void mLoopInvIterDo1() { \n" +
			"    int x = 1; \n" +
			"    //@ loop_invariant x != 0; \n" +
			"    Label: do { \n" +
			"      x = 0; \n" +
			"    } while (true); \n" +
			"  } \n" +
			" \n" +
			"  void mLoopInvInitFor() { \n" +
			"    //@ loop_invariant x != 0; \n" +
			"    for (int x = 0; x < 10; x++) { \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void mLoopInvIterFor() { \n" +
			"    //@ loop_invariant x == 0; \n" +
			"    for (int x = 0;; x++) { \n" +
			"    } \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_66() {
			this.runNegativeTest(new String[] {
			testsPath + "Hotspot.java", 
			"class HotspotInvariant0 { \n" +
			"  int hx;  //@ invariant hx == 0; \n" +
			"  // the default constructor fails to establish the following invariant \n" +
			"  int hs;  //@ invariant hs == 3; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_67() {
			this.runNegativeTest(new String[] {
			testsPath + "Hotspot.java", 
			"class HotspotInvariant1 { \n" +
			"  int hx = 2;  //@ invariant hx == 2; \n" +
			"  // the default constructor fails to establish the following invariant \n" +
			"  int hs = 2;  //@ invariant hs == 3; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_68() {
			this.runNegativeTest(new String[] {
			testsPath + "Hotspot.java", 
			"class SomeException extends Throwable { \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_69() {
			this.runNegativeTest(new String[] {
			testsPath + "label.java", 
			" \n" +
			"public class label { \n" +
			"   \n" +
			"  void r0_label_test() { \n" +
			"    int x; \n" +
			"    MyLabel: { \n" +
			"      x = 0; \n" +
			"      if (x == 0) \n" +
			"	break MyLabel; \n" +
			"      x = 1; \n" +
			"    } \n" +
			"    //@ assert x == 0; \n" +
			"  } \n" +
			"   \n" +
			"  void r1_label_test() { \n" +
			"    int x; \n" +
			"    MyLabel: x = 0; \n" +
			"    //@ assert x == 0; \n" +
			"  } \n" +
			"   \n" +
			"  void r2_label_test() { \n" +
			"    int x = 0; \n" +
			"    MyLabel: break MyLabel; \n" +
			"    //@ assert x == 0; \n" +
			"  } \n" +
			"   \n" +
			"  void r3_label_test() { \n" +
			"    int x; \n" +
			"    MyLabel: { \n" +
			"      x = 0; \n" +
			"      if (x == 2) \n" +
			"	break MyLabel; \n" +
			"      if (x == 0) \n" +
			"	break MyLabel; \n" +
			"      x = 1; \n" +
			"    } \n" +
			"    //@ assert x == 0; \n" +
			"  } \n" +
			" \n" +
			"  void r4_label_test() { \n" +
			"    MyLabel: ; \n" +
			"  } \n" +
			" \n" +
			"  void r5_label_test() { \n" +
			"    { MyLabel: ; } \n" +
			"    { MyLabel: ; } \n" +
			"  } \n" +
			" \n" +
			"  void r6_label_test() { \n" +
			"    int x = 0; \n" +
			"    Outer: { \n" +
			"      Inner: { \n" +
			"	break Outer; \n" +
			"      } \n" +
			"      x = 1; \n" +
			"    } \n" +
			"    //@ assert x == 0; \n" +
			"  } \n" +
			" \n" +
			"  void r7_label_test() { \n" +
			"    int x = 0; \n" +
			"    Outer: { \n" +
			"      Inner: { \n" +
			"	break Inner; \n" +
			"      } \n" +
			"      x = 1; \n" +
			"    } \n" +
			"    //@ assert x == 1; \n" +
			"  } \n" +
			" \n" +
			"  void r8_label_test() { \n" +
			"    int x = 0; \n" +
			"    MyLoop: \n" +
			"    while (x < 10) { \n" +
			"      x++; \n" +
			"    } \n" +
			"    //@ assert x == 10; \n" +
			"  } \n" +
			" \n" +
			"  void r9_label_test() { \n" +
			"    int x = 0; \n" +
			"    MyLoop: \n" +
			"    while (x < 10) { \n" +
			"      if (x == 5) \n" +
			"	break; \n" +
			"      x++; \n" +
			"    } \n" +
			"    //@ assert x == 5; \n" +
			"  } \n" +
			"   \n" +
			"  void r10_label_test() { \n" +
			"    int x = 0; \n" +
			"    MyLoop: \n" +
			"    while (x < 10) { \n" +
			"      if (x == 5) \n" +
			"	break MyLoop; \n" +
			"      x++; \n" +
			"    } \n" +
			"    //@ assert x == 5; \n" +
			"  } \n" +
			"   \n" +
			"  void r11_label_test() { \n" +
			"    //@ assert true; \n" +
			"    OuterLoop: \n" +
			"    while (true) { \n" +
			"      InnerLoop: \n" +
			"      while (true) { \n" +
			"	//@ assert true; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_70() {
			this.runNegativeTest(new String[] {
			testsPath + "Test.java", 
			"/** \n" +
			" ** This file tests that FindContributors includes the initialization \n" +
			" ** of ghost fields in superinterfaces properly. \n" +
			" **/ \n" +
			" \n" +
			"class Test { \n" +
			"    int k; \n" +
			"     \n" +
			"    Test() { \n" +
			"    } \n" +
			"} \n" +
			" \n" +
			"interface Intf { \n" +
			"    //@ ghost instance public int x; \n" +
			"    //@ invariant 0 < x; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_71() {
			this.runNegativeTest(new String[] {
			testsPath + "Test.java", 
			"class Sub extends Test implements Intf { \n" +
			"    Sub() { \n" +
			"        super(); \n" +
			"    }                             // error \n" +
			" \n" +
			"    Sub(int y) { \n" +
			"	//@ set x=3 \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_72() {
			this.runNegativeTest(new String[] {
			testsPath + "Test.java", 
			"class SubSub extends Sub implements Intf { \n" +
			"    SubSub() { \n" +
			"	super(3); \n" +
			"    } 			       // no error -- x is initialized only once \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_73() {
			this.runNegativeTest(new String[] {
			testsPath + "InterfaceInherit.java", 
			"interface A { \n" +
			"  //@ ghost instance public int a; \n" +
			"  //@ invariant -10 < a && a != 0 && a < 10; \n" +
			"  //@ ghost instance public int aZero; \n" +
			"  //@ invariant aZero < 10; \n" +
			"} \n" +
			" \n" +
			"interface B { \n" +
			"  //@ ghost instance /*@ non_null */ public int[] b; \n" +
			"} \n" +
			" \n" +
			"interface C extends A, B { \n" +
			"} \n" +
			" \n" +
			"interface D extends A { \n" +
			"  //@ ghost instance public int d; \n" +
			"  //@ invariant d != 0 && d <= a; \n" +
			"  //@ ghost instance public int dZero; \n" +
			"  //@ invariant 0 <= dZero; \n" +
			"  //@ invariant dZero <= aZero; \n" +
			"} \n" +
			" \n" +
			"class InterfaceInherit implements A, C { \n" +
			"  //@ ghost public int x; \n" +
			"  //@ invariant 10 <= x && x < 100; \n" +
			"  //@ ghost public int xZero; \n" +
			"  //@ invariant 0 <= xZero && xZero < 100; \n" +
			" \n" +
			"  //@ ghost public /*@ non_null */ Object y; \n" +
			"  Object w /*@ non_null */; \n" +
			" \n" +
			"  int z; \n" +
			"  //@ invariant 1 <= z; \n" +
			"  //@ invariant z < a; \n" +
			"  int zZero; \n" +
			"  //@ invariant -10 <= zZero; \n" +
			"  //@ invariant zZero <= aZero; \n" +
			" \n" +
			"  InterfaceInherit(int bad) { \n" +
			"  } \n" +
			" \n" +
			"  InterfaceInherit(double good) { \n" +
			"    //@ set a = 8; \n" +
			"    int[] bb = new int[120]; \n" +
			"    //@ set b = bb; \n" +
			"    //@ set x = a + 50; \n" +
			"    Object yy = new Object(); \n" +
			"    //@ set y = yy; \n" +
			"    z = 7; \n" +
			"    w = bb; \n" +
			"  } \n" +
			" \n" +
			"  void m(boolean b) { \n" +
			"    A a = this; \n" +
			"    //@ set a.a = 12; \n" +
			"    if (b) { \n" +
			"      p(a); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void p(A a) { \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_74() {
			this.runNegativeTest(new String[] {
			testsPath + "InterfaceInherit.java", 
			"class Sub extends InterfaceInherit implements D { \n" +
			"  Sub(int bad) { \n" +
			"    super(bad); \n" +
			"  } \n" +
			" \n" +
			"  Sub(double good) { \n" +
			"    super(good); \n" +
			"    //@ set d = a; \n" +
			"  } \n" +
			" \n" +
			"  Sub(Object yy, int xx) { \n" +
			"    super(0); \n" +
			"    //@ set d = a; \n" +
			"    //@ set x = xx; \n" +
			"    //@ set y = yy; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 45 <= xx && xx < 56; \n" +
			"  Sub(/*@ non_null */ Object yy, int xx, char zz) { \n" +
			"    super(0); \n" +
			"    //@ assert -10 <= zZero; \n" +
			"    //@ assert -10 <= aZero; \n" +
			"    //@ assert zZero < 10; \n" +
			"    //@ set aZero = (zZero == -10 ? 0 : (aZero < 0 ? -aZero : aZero)); \n" +
			"    //@ set dZero = aZero; \n" +
			"    //@ set d = a; \n" +
			"    //@ set x = xx; \n" +
			"    //@ set y = yy; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_75() {
			this.runNegativeTest(new String[] {
			testsPath + "Vanilla.java", 
			"class Vanilla { \n" +
			"  int k; \n" +
			" \n" +
			"  Vanilla() { \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_76() {
			this.runNegativeTest(new String[] {
			testsPath + "Vanilla.java", 
			"class Sub extends Vanilla { \n" +
			"  //@ invariant 0 < k; \n" +
			"   \n" +
			"  Sub() { \n" +
			"  }  // error:  fails to establish invariant 0 < k \n" +
			" \n" +
			"  //@ requires 0 < x; \n" +
			"  Sub(int x) { \n" +
			"    k = x; \n" +
			"  } \n" +
			"} \n" +
			" \n" +
			"interface A { \n" +
			"  //@ invariant 10 < ((Vanilla)this).k; \n" +
			"} \n" +
			" \n" +
			"interface B { \n" +
			"  //@ invariant ((Vanilla)this).k % 2 == 0; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_77() {
			this.runNegativeTest(new String[] {
			testsPath + "Vanilla.java", 
			"class Sub2 extends Vanilla implements A { \n" +
			"  Sub2() { \n" +
			"  }  // error:  fails to establish invariant 10 < k \n" +
			"} \n" +
			" \n" +
			"// The first constructor has \"k\" as a target, so it will pull in the \n" +
			"// invariant about \"k\".  The second constructor tests that the invariant \n" +
			"// is NOT pulled in on behalf of it being pulled in for the first constructor. \n" 
			}, "ERROR");
			}

			public void test_78() {
			this.runNegativeTest(new String[] {
			testsPath + "Vanilla.java", 
			"class Sub3 extends Vanilla implements A { \n" +
			"  Sub3() { \n" +
			"    k = 22; \n" +
			"  } \n" +
			"  Sub3(int x) { \n" +
			"  }  // error:  fails to establish invariant 10 < k \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_79() {
			this.runNegativeTest(new String[] {
			testsPath + "Vanilla.java", 
			"class Sub4 extends Sub implements A, B { \n" +
			"  Sub4() { \n" +
			"  }  // error:  fails to establish both 10 < k and k % 2 == 0 \n" +
			" \n" +
			"  //@ requires 10 < x && x % 2 == 0; \n" +
			"  Sub4(int x) { \n" +
			"    k = x; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_80() {
			this.runNegativeTest(new String[] {
			testsPath + "Vanilla.java", 
			"class SubSub extends Sub2 implements A, B { \n" +
			"  SubSub() { \n" 
			}, "ERROR");
			}

			public void test_81() {
			this.runNegativeTest(new String[] {
			testsPath + "Vanilla.java", 
			"  }  // error:  fails to establish k % 2 == 0  (superclass establishes 10 < k) \n" +
			" \n" +
			"  //@ requires 10 < x && x % 2 == 0; \n" +
			"  SubSub(int x) { \n" +
			"    k = x; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_82() {
			this.runNegativeTest(new String[] {
			testsPath + "SuperCallPost.java", 
			"class Super { \n" +
			"  int k; \n" +
			" \n" +
			"  Super() {  // is not required to establish invariant declared in subclass \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_83() {
			this.runNegativeTest(new String[] {
			testsPath + "SuperCallPost.java", 
			"class SuperCallPost extends Super { \n" +
			"  //@ invariant 10 <= k; \n" +
			" \n" +
			"  SuperCallPost() { \n" +
			"    super(); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 20 <= x && x <= Integer.MAX_VALUE; \n" +
			"  SuperCallPost(long x) { \n" +
			"    super(); \n" +
			"    k = (int)x; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_84() {
			this.runNegativeTest(new String[] {
			testsPath + "Body.java", 
			"interface A { \n" +
			"  //@ ghost instance public int a; \n" +
			"  //@ invariant 10 <= a; \n" +
			"} \n" +
			" \n" +
			"interface B { \n" +
			"  //@ ghost instance public int b; \n" +
			"  //@ invariant 10 <= b; \n" +
			"} \n" +
			" \n" +
			"interface C { \n" +
			"  //@ ghost instance public int c; \n" +
			"  //@ invariant 10 <= c; \n" +
			"} \n" +
			" \n" +
			"interface D { \n" +
			"  //@ ghost instance public int d; \n" +
			"  //@ invariant 10 <= d; \n" +
			"} \n" +
			" \n" +
			"class Super implements A, B { \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_85() {
			this.runNegativeTest(new String[] {
			testsPath + "Body.java", 
			"class Body extends Super implements A, C { \n" +
			"  int k; \n" +
			"  //@ invariant 10 <= k; \n" +
			" \n" +
			"  void m() { \n" +
			"    //@ set a = a; \n" +
			"    //@ set b = b; \n" +
			"    //@ set c = c; \n" +
			"    if (this instanceof D) { \n" +
			"      D d = (D)this; \n" +
			"      //@ set d.d = d.d; \n" +
			"    } \n" +
			"    k = k; \n" +
			"    if (this instanceof Sub) { \n" +
			"      Sub sub = (Sub)this; \n" +
			"      sub.s = sub.s; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  Body() { \n" +
			"    if (this instanceof Sub) { \n" +
			"      Sub sub = (Sub)this; \n" +
			"      //@ assert 10 <= sub.s;  // should fail, since invariant is declared in \n" 
			}, "ERROR");
			}

			public void test_86() {
			this.runNegativeTest(new String[] {
			testsPath + "Body.java", 
			"                               // Sub, Sub is a subclass of Body, and Body != Sub \n" +
			"    } \n" +
			"  }  //@ nowarn Invariant \n" +
			" \n" +
			"  Body(int q) { \n" +
			"    //@ assert 10 <= k;  // should fail, since no sibling is called \n" +
			"  }  //@ nowarn Invariant \n" +
			" \n" +
			"  Body(double q) { \n" +
			"    this((int)q); \n" +
			"    //@ assert 10 <= k;  // should succeed, since invariant is declared in Body \n" +
			"                         // and a sibling constructor is called \n" +
			"  }  // all invariants should pass, too \n" +
			" \n" +
			"  Body(int q0, int q1) { \n" +
			"    this(q0 + q1); \n" +
			"    if (this instanceof D) { \n" +
			"      D thisD = (D)this; \n" +
			"      //@ assert 10 <= thisD.d;  // should fail, since the invariant is declared in \n" +
			"                             // interface D, which is not a superinterface of Body, \n" +
			"                             // and this Body constructor calls a sibling \n" +
			"    } \n" +
			"  }  //@ nowarn Invariant \n" +
			" \n" +
			"  Body(int q0, int q1, int q2) { \n" +
			"    if (this instanceof C) { \n" +
			"      C thisC = (C)this; \n" +
			"      //@ assert 10 <= thisC.c;  // should fail, since C is a superinterface of \n" +
			"                     // Body, but not a superinterface of Body's superclass, \n" +
			"                     // and this Body constructor does not call a sibling \n" +
			"    } \n" +
			"  }  //@ nowarn Invariant \n" +
			" \n" +
			" \n" +
			"  Body(double q0, int q1) { \n" +
			"    //@ assert 10 <= this.a; \n" +
			"    //@ assert 10 <= this.b; \n" +
			"  }  //@ nowarn Invariant \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_87() {
			this.runNegativeTest(new String[] {
			testsPath + "Body.java", 
			"class Sub extends Body implements D { \n" +
			"  int s; \n" +
			"  //@ invariant 10 <= s; \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_88() {
			this.runNegativeTest(new String[] {
			testsPath + "Div.java", 
			"class Div { \n" +
			" \n" +
			"    //@ requires lo <= hi; \n" +
			"    //@ requires 0 <= lo; // FIXME - should not need this assumption \n" +
			"    void m(int lo, int hi) { \n" +
			"	int mid = (lo + hi)/2; \n" +
			"	//@ assert lo <= mid; \n" +
			"	//@ assert mid <= hi; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_89() {
			this.runNegativeTest(new String[] {
			testsPath + "final.java", 
			"final class C { \n" +
			"     \n" +
			"    /*@ helper */ C() {} \n" +
			" \n" +
			"    /*@ helper */ int m(int i) { \n" +
			"	return 34; \n" +
			"    } \n" +
			"     \n" +
			"    private int q() { \n" +
			"	return 22; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_90() {
			this.runNegativeTest(new String[] {
			testsPath + "chain1.java", 
			"class chain1 { \n" +
			"  void a() { \n" +
			"    int x; \n" +
			"    x = b(18); \n" +
			"    //@ assert x == 20; \n" +
			"    x = b(19); \n" +
			"    //@ assert x == 20;  // error \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private int b(int t) { \n" +
			"    return c(t+1); \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private int c(int t) { \n" +
			"    return d(t+1); \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private int d(int t) { \n" +
			"    return t; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_91() {
			this.runNegativeTest(new String[] {
			testsPath + "override.java", 
			"class C { \n" +
			"     \n" +
			"    int q() { \n" +
			"	return 22; \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_92() {
			this.runNegativeTest(new String[] {
			testsPath + "override.java", 
			"class D extends C { \n" +
			" \n" +
			"    /*@ helper */ final int q() { \n" +
			"	return 24; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_93() {
			this.runNegativeTest(new String[] {
			testsPath + "chain0.java", 
			"class chain0 { \n" +
			"  void a() { \n" +
			"    int x = b(18); \n" +
			"    //@ assert x == 18;  // warning, due to finite inlining \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private int b(int t) { \n" +
			"    return c(t); \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private int c(int t) { \n" +
			"    return c(t); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_94() {
			this.runNegativeTest(new String[] {
			testsPath + "Simple2.java", 
			"class Simple2 { \n" +
			"  Simple2() { \n" +
			"  } \n" +
			" \n" +
			"  int x; \n" +
			" \n" +
			"  void m() { \n" +
			"    int y = n(); \n" +
			"    //@ assert y == 5; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires -10 <= x; \n" +
			"  //@ helper \n" +
			"  private int n() { \n" +
			"    //@ assert 0 <= x; \n" +
			"    return x; \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures x == 5; \n" +
			"  private void p() { \n" +
			"    q0(); \n" +
			"    q1(); \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private void q0() { \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private void q1() { \n" +
			"    return; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_95() {
			this.runNegativeTest(new String[] {
			testsPath + "chain2.java", 
			"class chain2 { \n" +
			"  void m() { \n" +
			"    p(); \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private void p() { \n" +
			"    p(); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_96() {
			this.runNegativeTest(new String[] {
			testsPath + "restrictions2.java", 
			"class C { \n" +
			"     \n" +
			"    /*@ helper */ C() {} \n" +
			" \n" +
			"    /*@ helper */ int m(int i) { \n" +
			"	return 34; \n" +
			"    } \n" +
			"     \n" +
			"    private int q() { \n" +
			"	return 22; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_97() {
			this.runNegativeTest(new String[] {
			testsPath + "Constructor.java", 
			"class Constructor { \n" +
			"  /*@ non_null */ String s; \n" +
			" \n" +
			"  int x; \n" +
			"  //@ invariant 0 < x && x <= 10; \n" +
			" \n" +
			"  Constructor() { \n" +
			"    initFields(\"hello\", 8);  // okay \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private void initFields(String sp, int xp) { \n" +
			"    s = sp; \n" +
			"    x = xp; \n" +
			"  } \n" +
			" \n" +
			"  void initFieldsNonHelper0(String sp, int xp) { \n" +
			"    s = sp;  // violates non_null \n" +
			"    x = xp; \n" +
			"  }  // violates invariant \n" +
			" \n" +
			"  void initFieldsNonHelper1(String sp, int xp) { \n" +
			"    initFields(sp, xp);  // violates non_null inside this call \n" +
			"  }  // violates invariant \n" +
			" \n" +
			"  Constructor(String sp, int delta) { \n" +
			"    initFields(sp, 8);  // violates non_null inside this call \n" +
			"    x += delta; \n" +
			"  }  // violates x's invariant \n" +
			"  //@ requires delta >= 0; \n" +
			"  Constructor(int delta) { \n" +
			"    x = delta; \n" +
			"    initFields((String)null + (String)null, x + 1); \n" +
			"    x = x % 10; \n" +
			"    x++; \n" +
			"  }  // okay \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_98() {
			this.runNegativeTest(new String[] {
			testsPath + "restrictions.java", 
			"class C { \n" +
			"     \n" +
			"    /*@ helper */ C() {} \n" +
			" \n" +
			"    /*@ helper */ private int m(int i) { \n" +
			"	return 34; \n" +
			"    } \n" +
			"     \n" +
			"    private int q() { \n" +
			"	return 22; \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_99() {
			this.runNegativeTest(new String[] {
			testsPath + "restrictions.java", 
			"class D extends C { \n" +
			" \n" +
			"    /*@ helper */ int k; \n" +
			" \n" +
			"    /*@ helper */ private int q() { \n" +
			"	return 24; \n" +
			"    } \n" +
			" \n" +
			"    /*@ helper */ private int m(int i) { \n" +
			"	return 43; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_100() {
			this.runNegativeTest(new String[] {
			testsPath + "overload.java", 
			"class C { \n" +
			"     \n" +
			"    /*@ helper */ C() {} \n" +
			" \n" +
			"    /*@ helper */ static int m(int i) { \n" +
			"	return 34; \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_101() {
			this.runNegativeTest(new String[] {
			testsPath + "overload.java", 
			"class D extends C { \n" +
			" \n" +
			"    static int q(int i) { \n" +
			"	return m(i); \n" +
			"    } \n" +
			" \n" +
			"    /*@ helper */ static int m(int i) { \n" +
			"	return 43; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_102() {
			this.runNegativeTest(new String[] {
			testsPath + "Simple1.java", 
			"class Simple1 { \n" +
			"  Simple1() { \n" +
			"  } \n" +
			" \n" +
			"  int x; \n" +
			"   \n" +
			"  void m() { \n" +
			"    x = 5; \n" +
			"    int y = n(); \n" +
			"    //@ assert y == 5; \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private int n() { \n" +
			"    //@ assert 0 <= x; \n" +
			"    return x; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_103() {
			this.runNegativeTest(new String[] {
			testsPath + "postconditions.java", 
			"class C { \n" +
			"     \n" +
			"    /*@ non_null*/ Integer i; \n" +
			"    /*@ non_null*/ Integer j; \n" +
			"     \n" +
			"    //@ modifies i,j,this.*; \n" +
			"    C() { \n" +
			"	int k = init(4); \n" +
			"    } \n" +
			"    //@ modifies i,j; \n" +
			"    //@ ensures \\result == 4; \n" +
			"    /*@ helper */ private int init(int k) { \n" +
			"	i = new Integer(13); \n" +
			"	j = new Integer (55); \n" +
			"	return k; \n" +
			"    } \n" +
			"    //@ modifies i,j; \n" +
			"    void m(int x) { \n" +
			"        int k = init(x); \n" +
			"    }  // postcondition violation \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_104() {
			this.runNegativeTest(new String[] {
			testsPath + "Simple0.java", 
			"class Simple0 { \n" +
			"  Simple0() { \n" +
			"  } \n" +
			" \n" +
			"  int x; \n" +
			"   \n" +
			"  void m() { \n" +
			"    x = 5; \n" +
			"    int y = n(); \n" +
			"    //@ assert y == 5; \n" +
			"  } \n" +
			" \n" +
			"  private int n() { \n" +
			"    //@ assert 0 <= x; \n" +
			"    return x; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_105() {
			this.runNegativeTest(new String[] {
			testsPath + "recursive.java", 
			"class C { \n" +
			"     \n" +
			"    /*@ helper */ private void m() { \n" +
			"	q(); \n" +
			"    } \n" +
			" \n" +
			"    private void n() { \n" +
			"        m(); \n" +
			"    } \n" +
			" \n" +
			"    /*@ helper */ final void q() { \n" +
			"	r(); \n" +
			"    } \n" +
			"     \n" +
			"    /*@ helper */ final void r() { \n" +
			"	q(); \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_106() {
			this.runNegativeTest(new String[] {
			testsPath + "abstract.java", 
			"abstract class T { \n" +
			"  /*@ helper */ abstract void m(); \n" +
			"  /*@ helper */ native final void n(); \n" +
			"} \n" +
			" \n" +
			"interface J { \n" +
			"  /*@ helper */ void p(); \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_107() {
			this.runNegativeTest(new String[] {
			testsPath + "simple.java", 
			"class C { \n" +
			"     \n" +
			"    /*@ non_null*/ Integer i; \n" +
			"    /*@ non_null*/ Integer j; \n" +
			"     \n" +
			" \n" +
			"    C() { \n" +
			"	init(); \n" +
			"	init(); \n" +
			"	init(); \n" +
			"    } \n" +
			" \n" +
			"    /*@ helper */ private void init() { \n" +
			"	i = new Integer(13); \n" +
			"	j = new Integer (55); \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_108() {
			this.runNegativeTest(new String[] {
			testsPath + "notRecursive.java", 
			"class C { \n" +
			"     \n" +
			"    /*@ helper */ private void m() { \n" +
			"	q(); \n" +
			"    } \n" +
			" \n" +
			"    /*@ helper */ final void q() { \n" +
			"	r(); \n" +
			"    } \n" +
			"     \n" +
			"    final void r() { \n" +
			"	q(); \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_109() {
			this.runNegativeTest(new String[] {
			testsPath + "ghost.java", 
			"class Ghost22 { \n" +
			"  //@ ghost public int i; \n" +
			"  //@ghost public boolean b; \n" +
			" \n" +
			" //@invariant b && (b == true) && (i > 0); \n" +
			" \n" +
			"Ghost22() { \n" +
			"  //@set i= 6;  \n" +
			"  //@set b= true; \n" +
			"  if (this.m()) { \n" +
			"    //@set i= 6; \n" +
			"  } \n" +
			"  else { \n" +
			"    //@set i= -10; \n" +
			"} \n" +
			"} \n" +
			" \n" +
			"//@ requires true; \n" +
			"//@ ensures \\result == this.b; \n" +
			"boolean m() \n" +
			"{ }  //@nowarn Post; \n" +
			" \n" +
			" \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_110() {
			this.runNegativeTest(new String[] {
			testsPath + "LargeMagnitude.java", 
			"class LargeMagnitude { \n" +
			"  void m0() { \n" +
			"    //@ assert 0 <= 2000000; \n" +
			"    //@ assert -2000000 <= 0; \n" +
			"    //@ assert -2000000 < 2000000; \n" +
			"    //@ assert -8000000000L < -7999999999L; \n" +
			"    //@ assert -7999999999L <= -7999999999L; \n" +
			"    //@ assert -7999999999L <= 2; \n" +
			"    //@ assert -7999999999L <= 2000000; \n" +
			"    //@ assert -18 < 1234567890123L; \n" +
			"    //@ assert Long.MIN_VALUE < Integer.MIN_VALUE; \n" +
			"    //@ assert Integer.MIN_VALUE < Integer.MAX_VALUE; \n" +
			"    //@ assert Integer.MAX_VALUE < Long.MAX_VALUE; \n" +
			"    //@ assert 0x80000000 < 0x8f129400; \n" +
			"    //@ assert 0x8000000000000000L < 0x8f12940000000000L; \n" +
			"    //@ assert 0 < 0x7fffFFF; \n" +
			"    //@ assert 0 < 0x7fffFFFffffFFFFL; \n" +
			"  } \n" +
			" \n" +
			"  void m1() { \n" +
			"    long x = -7999999999L; \n" +
			"    //@ assert x < -7800648; \n" +
			"    //@ assert x - 1 == -8000000000L;  // escjava doesn't know this one \n" +
			"    //@ assert -2147483648 == 0x80000000; \n" +
			"    //@ assert -2147483647 == 0x80000001;  // escjava doesn't know this one \n" +
			"    //@ assert -2000000 == 0xffe17b80;  // escjava doesn't know this one \n" +
			"  } \n" +
			" \n" +
			"  final int k0 = 18; \n" +
			"  final int k1 = 1500000; \n" +
			"  static final int k2 = 2200000; \n" +
			"  final long k3 = 55000111; \n" +
			" \n" +
			"  //@ requires 0 <= in; \n" +
			"  //@ ensures 0 <= \\result; \n" +
			"  long m2(long in, int choice) { \n" +
			"    switch (choice) { \n" +
			"      case 0: \n" +
			"	return in + k0; \n" +
			"      case 1: \n" +
			"	return in + k1; \n" +
			"      case 2: \n" +
			"	return in + k2; \n" +
			"      case 3: \n" +
			"	return in + k3; \n" +
			"      default: \n" +
			"	return in; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 0 <= in; \n" +
			"  //@ ensures 0 <= \\result; \n" +
			"  long m3(long in, int choice) { \n" +
			"    return in + choice; \n" +
			"  }  // error:  return value may be negative \n" +
			" \n" +
			"  void m4() { \n" +
			"    //@ assert k0 < k1; \n" +
			"    //@ assert k1 < k2; \n" +
			"    //@ assert k2 < k3; \n" +
			" \n" +
			"    //@ assert k0 < 20 && 20 < k1; \n" +
			"    //@ assert k1 < 1700000 && 1700000 < k2; \n" +
			"    //@ assert k2 < 55000100 && 55000100 < k3; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_111() {
			this.runNegativeTest(new String[] {
			testsPath + "FinalFields.java", 
			"class FinalFields { \n" +
			"  static final int x = 16; \n" +
			"  static final boolean b0 = false; \n" +
			"  static final boolean b1 = ('W' < 'Q' ? false : 3 * 5 < 18); \n" +
			"  static final char ch = 'W'; \n" +
			"  static final String s = (\"hello\"); \n" +
			"  static final Object t = new Object(); \n" +
			"  static final int[] a = new int[false != true ? 24 % 5 * 3 : 3]; // 12 \n" +
			"  static final FinalFields[] aa = new FinalFields[a.length]; \n" +
			"  static final Object synonymForNull = null; \n" +
			"  static final int synonymForFive = 5; \n" +
			"  static final int[] av10 = {3, 2, 0}; \n" +
			"  static final int[] av11 = new int[] {3, 2, 0}; \n" +
			"  static final Object[] avo = new Object[] {\"hi\", \"hello\"}; \n" +
			"  static final Object[] avs = new String[] {\"hi\", \"hello\"}; \n" +
			"  static final Object[][] avmA = {{null, null}, {\"hello\"}, null}; \n" +
			"  static final Object[] avmB = new Object[12][40]; \n" +
			"  static final Object ss0 = \"hi\"; \n" +
			"  static final String ss1 = \"hello \" + \"there\"; \n" +
			"  static final String ss2 = \"hey\" + 12.5;  // this generates a String \n" +
			"  static final Object ss3 = (null + \"good\");  // this generates a String \n" +
			"  static final Object finalcast = (FinalClass)getObject(); \n" +
			" \n" +
			"  /*@ non_null */ static Object nnx; \n" +
			" \n" +
			"  //@ requires x == 16; \n" +
			"  //@ requires !b0; \n" +
			"  //@ requires b1; \n" +
			"  //@ requires ch == 'W'; \n" +
			"  //@ requires ch != 'Q'; \n" +
			"  //@ requires s != null; \n" +
			"  //@ requires t != null; \n" +
			"  //@ requires \\typeof(t) == \\type(Object); \n" +
			"  //@ requires a != null; \n" +
			"  //@ requires \\typeof(a) == \\type(int[]); \n" +
			"  //@ requires a.length == 12; \n" +
			"  //@ requires aa != null; \n" +
			"  //@ requires \\typeof(aa) == \\type(FinalFields[]); \n" +
			"  //@ requires synonymForNull == null; \n" +
			"  //@ requires synonymForFive == 5; \n" +
			"  //@ requires av10 != null; \n" +
			"  //@ requires \\typeof(av10) == \\type(int[]); \n" +
			"  //@ requires av10.length == 3; \n" +
			"  //@ requires av11 != null; \n" +
			"  //@ requires \\typeof(av11) == \\type(int[]); \n" +
			"  //@ requires av11.length == 3; \n" +
			"  //@ requires avo != null; \n" +
			"  //@ requires \\typeof(avo) == \\type(Object[]); \n" +
			"  //@ requires avo.length == 2; \n" +
			"  //@ requires avs != null; \n" +
			"  //@ requires \\typeof(avs) == \\type(String[]); \n" +
			"  //@ requires avs.length == 2; \n" +
			"  //@ requires avmA != null; \n" +
			"  //@ requires avmA.length == 3; \n" +
			"  //@ requires \\typeof(avmA) == \\type(Object[][]); \n" +
			"  //@ requires avmB != null; \n" +
			"  //@ requires avmB.length == 12;  // not 40 \n" +
			"  //@ requires \\typeof(avmB) == \\type(Object[][]); \n" +
			"  //@ requires ss0 != null; \n" +
			"  //@ requires \\typeof(ss0) == \\type(String); \n" +
			"  //@ requires ss1 != null; \n" +
			"  //@ requires \\typeof(ss1) == \\type(String); \n" +
			"  //@ requires ss2 != null; \n" +
			"  //@ requires \\typeof(ss2) == \\type(String); \n" +
			"  //@ requires ss3 != null; \n" +
			"  //@ requires \\typeof(ss3) == \\type(String); \n" +
			"  //@ requires finalcast == null || finalcast instanceof FinalClass; \n" +
			"  //@ requires finalcast == null || \\typeof(finalcast) == \\type(FinalClass); \n" +
			"  //@ requires finalcast == (FinalClass)finalcast; \n" +
			"  private static void checkStaticFieldInitializers() { \n" +
			"    /*@ assert av10[1] == 2; */  // this must fail, since the initial value of 2 may be changed \n" +
			"    /*@ assert avmA[0].length == 2; */  // this must fail, for the same reason \n" +
			"  } \n" +
			"   \n" +
			"  final int ix = 16; \n" +
			"  final boolean ib0 = false; \n" +
			"  final boolean ib1 = ('W' < 'Q' ? false : 3 * 5 < 18); \n" +
			"  static final char ich = 'Q'; \n" +
			"  final String is = (\"hello\"); \n" +
			"  final Object it = new Object(); \n" +
			"  final int[] ia = new int[ix - 4]; // 12 \n" +
			"  final FinalFields[] iaa = new FinalFields[a.length]; \n" +
			"  final Object anotherSynonymForNull = null; \n" +
			"  static final int anotherSynonymForFive = 5; \n" +
			"  static final int[] iav10 = {3, 2, 0}; \n" +
			"  static final int[] iav11 = new int[] {3, 2, 0}; \n" +
			"  static final Object[] iavo = new Object[] {\"hi\", \"hello\"}; \n" +
			"  static final Object[] iavs = new String[] {\"hi\", \"hello\"}; \n" +
			"  final Object[][] iavmA = {{null, null}, {\"hello\"}, null}; \n" +
			"  final Object[] iavmB = new Object[12][40]; \n" +
			"  final Object iss0 = \"hi\"; \n" +
			"  final String iss1 = \"hello \" + \"there\"; \n" +
			"  final String iss2 = \"hey\" + 12.5;  // this generates a String \n" +
			"  final Object iss3 = (null + \"good\");  // this generates a String \n" +
			"  final Object ifinalcast = (FinalClass)getObject(); \n" +
			" \n" +
			"  /*@ non_null */ Object innx; \n" +
			" \n" +
			"  //@ requires ix == 16; \n" +
			"  //@ requires !ib0; \n" +
			"  //@ requires ib1; \n" +
			"  //@ requires ich != 'W'; \n" +
			"  //@ requires ich == 'Q'; \n" +
			"  //@ requires is != null; \n" +
			"  //@ requires it != null; \n" +
			"  //@ requires \\typeof(it) == \\type(Object); \n" +
			"  //@ requires ia != null; \n" +
			"  //@ requires \\typeof(ia) == \\type(int[]); \n" +
			"  //@ requires ia.length == 12; \n" +
			"  //@ requires iaa != null; \n" +
			"  //@ requires \\typeof(iaa) == \\type(FinalFields[]); \n" +
			"  //@ requires anotherSynonymForNull == null; \n" +
			"  //@ requires anotherSynonymForFive == 5; \n" +
			"  //@ requires iav10 != null; \n" +
			"  //@ requires \\typeof(iav10) == \\type(int[]); \n" +
			"  //@ requires iav10.length == 3; \n" +
			"  //@ requires iav11 != null; \n" +
			"  //@ requires \\typeof(iav11) == \\type(int[]); \n" +
			"  //@ requires iav11.length == 3; \n" +
			"  //@ requires iavo != null; \n" +
			"  //@ requires \\typeof(iavo) == \\type(Object[]); \n" +
			"  //@ requires iavo.length == 2; \n" +
			"  //@ requires iavs != null; \n" +
			"  //@ requires \\typeof(iavs) == \\type(String[]); \n" +
			"  //@ requires iavs.length == 2; \n" +
			"  //@ requires iavmA != null; \n" +
			"  //@ requires iavmA.length == 3; \n" +
			"  //@ requires \\typeof(iavmA) == \\type(Object[][]); \n" +
			"  //@ requires iavmB != null; \n" +
			"  //@ requires iavmB.length == 12;  // not 40 \n" +
			"  //@ requires \\typeof(iavmB) == \\type(Object[][]); \n" +
			"  //@ requires iss0 != null; \n" +
			"  //@ requires \\typeof(iss0) == \\type(String); \n" +
			"  //@ requires iss1 != null; \n" +
			"  //@ requires \\typeof(iss1) == \\type(String); \n" +
			"  //@ requires iss2 != null; \n" +
			"  //@ requires \\typeof(iss2) == \\type(String); \n" +
			"  //@ requires iss3 != null; \n" +
			"  //@ requires \\typeof(iss3) == \\type(String); \n" +
			"  //@ requires ifinalcast == null || ifinalcast instanceof FinalClass; \n" +
			"  //@ requires ifinalcast == null || \\typeof(ifinalcast) == \\type(FinalClass); \n" +
			"  //@ requires ifinalcast == (FinalClass)ifinalcast; \n" +
			"  private void checkInstanceFieldInitializers() { \n" +
			"    /*@ assert iav10[1] == 2; */  // this must fail, since the initial value of 2 may be changed \n" +
			"    /*@ assert iavmA[0].length == 2; */  // this must fail, for the same reason \n" +
			"  } \n" +
			" \n" +
			"  FinalFields() { \n" +
			"    checkStaticFieldInitializers(); \n" +
			"    /*@ assert innx != null; */  // this will fail, by design (since innx should not be used here) \n" +
			"    innx = new Object(); \n" +
			"    checkInstanceFieldInitializers(); \n" +
			"    // just make sure checker gets this far \n" +
			"    int localA, localB; \n" +
			"    //@ assert localA < localB;  // warns if checker gets here, which is good \n" +
			"  } \n" +
			" \n" +
			"  FinalFields(int j) { \n" +
			"    this(); \n" +
			"    checkStaticFieldInitializers(); \n" +
			"    /*@ assert innx != null; */ \n" +
			"    checkInstanceFieldInitializers(); \n" +
			"  } \n" +
			" \n" +
			"  void m() { \n" +
			"    checkStaticFieldInitializers(); \n" +
			"    checkInstanceFieldInitializers(); \n" +
			"  } \n" +
			" \n" +
			"  static void p() { \n" +
			"    checkStaticFieldInitializers(); \n" +
			"  } \n" +
			" \n" +
			"  static void q(/*@ non_null */ FinalFields ffParam) { \n" +
			"    ffParam.checkInstanceFieldInitializers(); \n" +
			"    FinalFields ffNew = new FinalFields(); \n" +
			"    ffParam.checkInstanceFieldInitializers(); \n" +
			"    ffNew.checkInstanceFieldInitializers(); \n" +
			"    checkStaticFieldInitializers(); \n" +
			"  } \n" +
			" \n" +
			"  static Object getObject() { \n" +
			"    return null; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_112() {
			this.runNegativeTest(new String[] {
			testsPath + "FinalFields.java", 
			"final class FinalClass { \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_113() {
			this.runNegativeTest(new String[] {
			testsPath + "NonFinalClasses.java", 
			"class NonFinalClasses { \n" +
			"  static final Object x0 = getNotAFinalClassObject(); \n" +
			"  static final NotFinalClass x1 = getNotAFinalClassObject(); \n" +
			"  static final /*@ non_null */ Object x2 = getNotAFinalClassObject(); \n" +
			"  static final /*@ non_null */ NotFinalClass x3 = getNotAFinalClassObject(); \n" +
			"  static final Object a0 = ma0(); \n" +
			"  static final Object a1 = ma1(); \n" +
			"  static final Object a2 = ma2(); \n" +
			"  static final Object a3 = ma3(); \n" +
			" \n" +
			"  static void testStatic() { \n" +
			"    //@ assert x0 == null || x0 instanceof NotFinalClass; \n" +
			"    //@ assert x0 == null || \\typeof(x0) == \\type(NotFinalClass); // fail \n" +
			"    //@ assert x1 == null || x1 instanceof NotFinalClass; \n" +
			"    //@ assert x1 == null || \\typeof(x1) == \\type(NotFinalClass); // fail \n" +
			"    //@ assert x2 != null; \n" +
			"    //@ assert x0 instanceof NotFinalClass;        // fail \n" +
			"    //@ assert x3 != null; \n" +
			"    //@ assert x3 instanceof NotFinalClass; \n" +
			"    //@ assert \\typeof(x3) == \\type(NotFinalClass);  // fail \n" +
			"     \n" +
			"    //@ assert a0 == null || a0 instanceof YesAFinalClass[]; \n" +
			"    //@ assert a1 == null || a1 instanceof YesAFinalClass[][]; \n" +
			"    //@ assert a2 == null || a2 instanceof NotFinalClass[]; \n" +
			"    //@ assert a3 == null || a3 instanceof NotFinalClass[][]; \n" +
			"    //@ assert a0 == null || \\typeof(a0) == \\type(YesAFinalClass[]); \n" +
			"    //@ assert a1 == null || \\typeof(a1) == \\type(YesAFinalClass[][]); \n" +
			"    //@ assert a2 == null || \\typeof(a2) == \\type(NotFinalClass[]);    // fail \n" +
			"    //@ assert a3 == null || \\typeof(a3) == \\type(NotFinalClass[][]);  // fail \n" +
			"  } \n" +
			" \n" +
			"  final Object ix0 = getNotAFinalClassObject(); \n" +
			"  final NotFinalClass ix1 = getNotAFinalClassObject(); \n" +
			"  final /*@ non_null */ Object ix2 = getNotAFinalClassObject(); // non_null fail \n" +
			"  final /*@ non_null */ NotFinalClass ix3 = getNotAFinalClassObject(); // non_null fail \n" +
			"  final Object ia0 = ma0(); \n" +
			"  final Object ia1 = ma1(); \n" +
			"  final Object ia2 = ma2(); \n" +
			"  final Object ia3 = ma3(); \n" +
			" \n" +
			"  NonFinalClasses() { \n" +
			"  } // ix2 and ix3 are not necessarily non-null here \n" +
			" \n" +
			"  void testInstance() { \n" +
			"    //@ assert ix0 == null || ix0 instanceof NotFinalClass; \n" +
			"    //@ assert ix0 == null || \\typeof(ix0) == \\type(NotFinalClass); // fail \n" +
			"    //@ assert ix1 == null || ix1 instanceof NotFinalClass; \n" +
			"    //@ assert ix1 == null || \\typeof(ix1) == \\type(NotFinalClass); // fail \n" +
			"    //@ assert ix2 != null; \n" +
			"    //@ assert ix0 instanceof NotFinalClass;        // fail \n" +
			"    //@ assert ix3 != null; \n" +
			"    //@ assert ix3 instanceof NotFinalClass; \n" +
			"    //@ assert \\typeof(ix3) == \\type(NotFinalClass);  // fail \n" +
			"     \n" +
			"    //@ assert ia0 == null || ia0 instanceof YesAFinalClass[]; \n" +
			"    //@ assert ia1 == null || ia1 instanceof YesAFinalClass[][]; \n" +
			"    //@ assert ia2 == null || ia2 instanceof NotFinalClass[]; \n" +
			"    //@ assert ia3 == null || ia3 instanceof NotFinalClass[][]; \n" +
			"    //@ assert ia0 == null || \\typeof(ia0) == \\type(YesAFinalClass[]); \n" +
			"    //@ assert ia1 == null || \\typeof(ia1) == \\type(YesAFinalClass[][]); \n" +
			"    //@ assert ia2 == null || \\typeof(ia2) == \\type(NotFinalClass[]);    // fail \n" +
			"    //@ assert ia3 == null || \\typeof(ia3) == \\type(NotFinalClass[][]);  // fail \n" +
			"  } \n" +
			" \n" +
			"  void testLocal() { \n" +
			"    Object lx0 = getNotAFinalClassObject(); \n" +
			"    NotFinalClass lx1 = getNotAFinalClassObject(); \n" +
			"    /*@ non_null */ Object lx2 = getNotAFinalClassObject();  // non_null fail \n" +
			"    /*@ non_null */ NotFinalClass lx3 = getNotAFinalClassObject(); // non_null fail \n" +
			" \n" +
			"    //@ assert lx0 == null || lx0 instanceof NotFinalClass; \n" +
			"    //@ assert lx0 == null || \\typeof(lx0) == \\type(NotFinalClass); // fail \n" +
			"    //@ assert lx1 == null || lx1 instanceof NotFinalClass; \n" +
			"    //@ assert lx1 == null || \\typeof(lx1) == \\type(NotFinalClass); // fail \n" +
			"    //@ assert lx2 != null; \n" +
			"    //@ assert lx2 instanceof NotFinalClass; \n" +
			"    //@ assert lx3 != null; \n" +
			"    //@ assert lx3 instanceof NotFinalClass; \n" +
			"    //@ assert \\typeof(lx3) == \\type(NotFinalClass);  // fail \n" +
			" \n" +
			"    Object la0 = ma0(); \n" +
			"    Object la1 = ma1(); \n" +
			"    Object la2 = ma2(); \n" +
			"    Object la3 = ma3(); \n" +
			"    //@ assert la0 != null && la1 != null; \n" +
			"    //@ assert la2 != null && la3 != null; \n" +
			"    //@ assert la0 instanceof YesAFinalClass[]; \n" +
			"    //@ assert la1 instanceof YesAFinalClass[][]; \n" +
			"    //@ assert la2 instanceof NotFinalClass[]; \n" +
			"    //@ assert la3 instanceof NotFinalClass[][]; \n" +
			"    //@ assert \\typeof(la0) == \\type(YesAFinalClass[]); \n" +
			"    //@ assert \\typeof(la1) == \\type(YesAFinalClass[][]); \n" +
			"    //@ assert \\typeof(la2) == \\type(NotFinalClass[]);    // fail \n" +
			"    //@ assert \\typeof(la3) == \\type(NotFinalClass[][]);  // fail \n" +
			"  } \n" +
			" \n" +
			"  static NotFinalClass getNotAFinalClassObject() { \n" +
			"    return null; \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != null; \n" +
			"  static YesAFinalClass[] ma0() { \n" +
			"    return new YesAFinalClass[10]; \n" +
			"  }; \n" +
			"  //@ ensures \\result != null; \n" +
			"  static YesAFinalClass[][] ma1() { \n" +
			"    if (a0 == null) { \n" +
			"      return new YesAFinalClass[10][20]; \n" +
			"    } else { \n" +
			"      return new YesAFinalClass[10][]; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != null; \n" +
			"  static NotFinalClass[] ma2() { \n" +
			"    return new NotFinalClass[10]; \n" +
			"  } \n" +
			"  //@ ensures \\result != null; \n" +
			"  static NotFinalClass[][] ma3() { \n" +
			"    return new NotFinalClass[10][20]; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_114() {
			this.runNegativeTest(new String[] {
			testsPath + "NonFinalClasses.java", 
			"class NotFinalClass { \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_115() {
			this.runNegativeTest(new String[] {
			testsPath + "NonFinalClasses.java", 
			"final class YesAFinalClass { \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_116() {
			this.runNegativeTest(new String[] {
			testsPath + "NonFinalClasses.java", 
			"class PrimitiveArrays { \n" +
			"  final static Object arr = m(); \n" +
			"  static int[] m() { return null; } \n" +
			"  static void p() { \n" +
			"    //@ assert arr == null || arr instanceof int[]; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_117() {
			this.runNegativeTest(new String[] {
			testsPath + "TestConstants.java", 
			"class TestConstants { \n" +
			" \n" +
			"  static final boolean t = true; \n" +
			" \n" +
			"  static final int i = 1; \n" +
			"  static final char c = 'a'; \n" +
			"  static final byte b = 2; \n" +
			"  static final short s = 3; \n" +
			"  static final long l = 4; \n" +
			" \n" +
			"  static final float f = 100; \n" +
			"  static final double d = 1.3; \n" +
			" \n" +
			"  static final String ss = \"hello\"; \n" +
			"  static final String sr = null; \n" +
			" \n" +
			"  static final String[] arg = { \"hello\", \"there\" }; \n" +
			" \n" +
			"  static final long minLong = 0x8000000000000000L; \n" +
			" \n" +
			" \n" +
			"  // no errors in this one... \n" +
			"  void testPos() { \n" +
			"    //@ assert t \n" +
			" \n" +
			"    //@ assert i+c+b+s+l == 1+'a'+2+3+4 \n" +
			" \n" +
			"    //@ assert f == 100 \n" +
			"    //@ assert d == 1.3 \n" +
			" \n" +
			"    ss.equals(arg[0]); \n" +
			"    ss.equals(arg[1]); \n" +
			" \n" +
			"    // Make sure we can handle converting minLong to a symbolic string: \n" +
			"    //@ assert minLong == minLong \n" +
			"  } \n" +
			" \n" +
			" \n" +
			"  void testNeg1() { \n" +
			"    sr.equals(\"hello\");		// error \n" +
			"  } \n" +
			" \n" +
			"  void testNeg2() { \n" +
			"    ss.equals(arg[3]);		// error \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_118() {
			this.runNegativeTest(new String[] {
			testsPath + "TestConstants.java", 
			"class EqualConstants { \n" +
			"  static final int X = 12; \n" +
			"  static final int Y = X; \n" +
			"  static final int Z = X + 1 + Y; \n" +
			" \n" +
			"  void m0() { \n" +
			"    //@ assert X == 12; \n" +
			"  } \n" +
			" \n" +
			"  void m1() { \n" +
			"    //@ assert Y == 12; \n" +
			"  } \n" +
			" \n" +
			"  void m2() { \n" +
			"    //@ assert X == Y; \n" +
			"  } \n" +
			" \n" +
			"  void m3() { \n" +
			"    //@ assert Z == 25; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_119() {
			this.runNegativeTest(new String[] {
			testsPath + "NegByte.java", 
			"class NegByte { \n" +
			"  static final byte b = (byte)0xFF;  // caused escjava 1.2.2 to crash \n" +
			" \n" +
			"  //@ ensures \\result == -1; \n" +
			"  int m() { \n" +
			"    //@ assert a == a;  // make sure 'a' gets placed in back pred \n" +
			"    //@ assert b == b;  // make sure 'b' gets placed in back pred \n" +
			"    byte c = (byte)0xFF; \n" +
			"    return c; \n" +
			"  }  // escjava does not know that dynamically casting 0xFF to byte yields -1 \n" +
			" \n" +
			"  static final Object[] a = new Object[(byte)0xFF];  // caused escjava 1.2.2 to crash \n" +
			" \n" +
			"  Object[] a0 = new Object[(byte)0x3F]; \n" +
			"  Object[] a1 = new Object[(byte)0xF3];  // neg array size! \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_120() {
			this.runNegativeTest(new String[] {
			testsPath + "C1.java", 
			"class C { \n" +
			"    /*@ non_null */ int [] a; // = new int[10]; \n" +
			"    /*@ non_null */ int [] b; // = new int[10];  \n" +
			"    /*@ invariant (\\forall int i; 0 <= i && i < b.length ==> b[i] != 0); */ \n" +
			" \n" +
			"    C () { \n" +
			"	/*@  \n" +
			"	  loop_invariant i >= 0; \n" +
			"	  loop_invariant (\\forall int j; 0 <= j && j < i ==> b[j] != 0); \n" +
			"	  loop_invariant (\\forall int [] z; z != b ==> (\\forall int j; z[j] == \\old(z[j]))); \n" +
			"	*/ \n" +
			"	for (int i = 0; i < b.length; i++) { \n" +
			"	    b[i] = 1; \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    /*@ ensures (\\forall int i; 0 <= i && i < a.length ==> a[i] == 0); */ \n" +
			"    void Zero () { \n" +
			"	b = b; \n" +
			"	/*@ loop_invariant i >= 0; \n" +
			"	    loop_invariant (\\forall int j; 0 <= j && j < i ==> a[j] == 0); */ \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			"	    a[i] = 0;	 \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    /*@ ensures (\\forall int i; 0 <= i && i < a.length ==> a[i] == 0); */ \n" +
			"    void ZeroBad1 () { \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			"	    a[i] = 0;	// warning expected  \n" +
			"	}  \n" +
			"    } // warning expected  \n" +
			" \n" +
			"    void ZeroBad2 () { \n" +
			"	/*@ loop_invariant i >= 0; \n" +
			"	    loop_invariant (\\forall int j; 0 <= j && j < i ==> a[j] == 0); */ \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			"	    a[i] = 0;	 \n" +
			"	    a = a; \n" +
			"	} \n" +
			"    } // warning expected \n" +
			" \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_121() {
			this.runNegativeTest(new String[] {
			testsPath + "AllocTest.java", 
			"/*  \n" +
			" * This test checks that if alloc is the target of a loop then it is  \n" +
			" * havoced to a value greater than its value just before the loop begins. \n" +
			" */ \n" +
			" \n" +
			"class AllocTest { \n" +
			" \n" +
			"    int i = 5; \n" +
			"    //@ invariant i > 0; \n" +
			" \n" +
			"    void m(int n) { \n" +
			" \n" +
			"	//@ loop_invariant (\\forall AllocTest a; a.i > 0); \n" +
			"	while (i < n) { \n" +
			"	    //@ assert i > 0; \n" +
			"	    i = i + 1; \n" +
			"            int[] junk = new int[10]; \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_122() {
			this.runNegativeTest(new String[] {
			testsPath + "C3.java", 
			"class C3 { \n" +
			"    int y; \n" +
			"    int z; \n" +
			" \n" +
			"    void Foo () { \n" +
			"	int x = 0; \n" +
			"	/*@  \n" +
			"	  loop_invariant y == \\old(y);  \n" +
			"	  loop_invariant x == \\old(x); \n" +
			"	  loop_invariant (\\forall C3 o; o != this ==> o.z == \\old(o.z));  \n" +
			"	  loop_invariant (\\forall C3 o; o.y == \\old(o.y));  \n" +
			"	  loop_invariant (\\forall C3 o; o.z == \\old(o.z));  \n" +
			"	*/ \n" +
			"	while (true) { \n" +
			"	    y = y + 1 - 1; \n" +
			"	    x = x + 1 - 1; \n" +
			"	    z = z + 1; \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    void Goo () { \n" +
			"	C3 x; \n" +
			"	/*@ assume (\\forall C3 a; a.y == a.z); */ \n" +
			"	/*@ loop_invariant (\\forall C3 a; !\\fresh(a) ==> a.y == a.z); */ \n" +
			"	while (true) { \n" +
			"	    x = new C3(); \n" +
			"	    x.y = 1; \n" +
			"	    x.z = 0; \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    void Loo () { \n" +
			"	C3 x; \n" +
			"	/*@ loop_invariant (\\forall C3 a; \\fresh(a) ==> a.y == a.z); */ \n" +
			"	while (true) { \n" +
			"	    x = new C3(); \n" +
			"	    x.y = 0; \n" +
			"	    x.z = 0; \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    /*@ ensures (\\forall C3 a; \\fresh(a) ==> a == this); */ //@ nowarn \n" +
			"    public C3() { \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_123() {
			this.runNegativeTest(new String[] {
			testsPath + "C2.java", 
			"class C2 { \n" +
			"    /*@ non_null */ static int [] a = new int[10]; \n" +
			"    /*@ non_null */ static int [] b = new int[10];  \n" +
			"    /*@ invariant (\\forall int i; 0 <= i && i < b.length ==> b[i] != 0); */ \n" +
			" \n" +
			"    C2 () { \n" +
			"	/*@ loop_invariant i >= 0; \n" +
			"	    loop_invariant (\\forall int j; 0 <= j && j < i ==> b[j] != 0); */ \n" +
			"	for (int i = 0; i < b.length; i++) { \n" +
			"	    b[i] = 1; \n" +
			"	} \n" +
			" \n" +
			"	/*@ assert (\\forall int i; 0 <= i && i < b.length ==> b[i] != 0); */ \n" +
			"    } \n" +
			" \n" +
			"    /*@ ensures (\\forall int i; 0 <= i && i < a.length ==> a[i] == 0); */ \n" +
			"    void Zero () { \n" +
			"	/*@ loop_invariant i >= 0; \n" +
			"	    loop_invariant (\\forall int j; 0 <= j && j < i ==> a[j] == 0); */ \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			"	    a[i] = 0;	 \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    /*@ ensures (\\forall int i; 0 <= i && i < a.length ==> a[i] == 0); */ \n" +
			"    void ZeroBad1 () { \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			"	    a[i] = 0;	// warning expected  \n" +
			"	}  \n" +
			"    } // warning expected  \n" +
			" \n" +
			"    void ZeroBad2 () { \n" +
			"	/*@ loop_invariant i >= 0; \n" +
			"	    loop_invariant (\\forall int j; 0 <= j && j < i ==> a[j] == 0); */ \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			"	    a[i] = b[i];	 \n" +
			"	    a[i] = 0; \n" +
			"	    a = a; \n" +
			"	} \n" +
			"    } // warning expected \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_124() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"public class C { \n" +
			"    public static void test1() { \n" +
			"	int x=1; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	x = x+x; \n" +
			"	//@ assert x==4096; \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_125() {
			this.runNegativeTest(new String[] {
			testsPath + "trycatch2.java", 
			"class Try2 { \n" +
			"  //@ requires t != null; \n" +
			"  void m1(Throwable t) throws Throwable { \n" +
			"    int x,y; \n" +
			"    try { \n" +
			"      x=0; \n" +
			"      //@ assume \\typeof(t) == \\type(Throwable); \n" +
			"      throw t; \n" +
			"    } catch(RuntimeException t3) { \n" +
			"      x=3; \n" +
			"    } \n" +
			" \n" +
			"    //@ assert x==0; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_126() {
			this.runNegativeTest(new String[] {
			testsPath + "sync.java", 
			"class Sync { \n" +
			" \n" +
			"  Sync c,d; \n" +
			"  void m1() { \n" +
			"    //@ assume this.c != null && this.d != null; \n" +
			"    //@ assume \\max(\\lockset) < this.c; \n" +
			"    //@ assume this.c < this.d; \n" +
			"    synchronized(this.c) { \n" +
			"      synchronized(this.d) { \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  void m2() { \n" +
			"    //@ assume \\lockset[this]; \n" +
			"    synchronized(this) { \n" +
			"      synchronized(this) { \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m3() { \n" +
			"    //@ assume \\max(\\lockset) < this; \n" +
			"    synchronized(this) { \n" +
			"      synchronized(this) { \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  synchronized void m4() { \n" +
			"    synchronized(this) { \n" +
			"      synchronized(this) { \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  static synchronized void m5() { \n" +
			"    //@ assert \\lockset[Sync.class]; \n" +
			"  } \n" +
			" \n" +
			"  synchronized void m6() { \n" +
			"    /*@ assert \\lockset[Sync.class]; */  // no way, Jose \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_127() {
			this.runNegativeTest(new String[] {
			testsPath + "sync.java", 
			"class SyncAxiom { \n" +
			"  Object mu, nu; \n" +
			"  //@ invariant nu != null; \n" +
			"  SyncAxiom() { \n" +
			"    mu = new Object(); \n" +
			"    nu = new Object(); \n" +
			"  } \n" +
			"   \n" +
			"  //@ axiom (\\forall SyncAxiom s; s < s.nu); \n" +
			"  //@ axiom (\\forall SyncAxiom s; s.mu != null ==> s < s.mu && s.mu < s.nu); \n" +
			"   \n" +
			"  /*@ monitored */ int x; \n" +
			"  /*@ monitored_by mu; */ int y; \n" +
			"  /*@ monitored_by nu; */ int z; \n" +
			"  /*@ monitored_by mu, nu; */ int w; \n" +
			"  /*@ monitored_by this; */ int v; \n" +
			"  /*@ monitored_by this, mu; */ int u; \n" +
			" \n" +
			"  synchronized int m0() { // fails (Deadlock) \n" +
			"    synchronized (mu) { // fails (Null) \n" +
			"      synchronized (nu) { \n" +
			"	return x; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this || \\lockset[this]; \n" +
			"  //@ requires mu != null; \n" +
			"  synchronized int m1() { \n" +
			"    synchronized (mu) { // fails (Deadlock) \n" +
			"      synchronized (nu) { \n" +
			"	return x; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this || \\lockset[this]; \n" +
			"  //@ requires mu != null && \\max(\\lockset) < mu; \n" +
			"  synchronized int m2() { \n" +
			"    synchronized (mu) { \n" +
			"      synchronized (nu) { \n" +
			"	x = y = z = w = v = u = 2; \n" +
			"	return x + y + z + w + v + u; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this || \\lockset[this]; \n" +
			"  synchronized int m3() { \n" +
			"    x = v = 3; \n" +
			"    return x + u + v; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this; \n" +
			"  int m4() { \n" +
			"    if (mu == null) { \n" +
			"      synchronized (this) { \n" +
			"	x = v = u = 4; \n" +
			"	return x + v + u; \n" +
			"      } \n" +
			"    } else { \n" +
			"      synchronized (mu) { \n" +
			"	y = 4; \n" +
			"	int i = y + u; \n" +
			"	return i + x;  // fails on reading x \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this; \n" +
			"  void m5() { \n" +
			"    if (mu == null) { \n" +
			"      synchronized (this) { \n" +
			"	u = 5; \n" +
			"      } \n" +
			"      synchronized (nu) { \n" +
			"	int i = w; \n" +
			"	w = i + 1; \n" +
			"      } \n" +
			"    } else { \n" +
			"      synchronized (mu) { \n" +
			"	int i = w; \n" +
			"	w = i + 1; // fails \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this; \n" +
			"  int m6() { \n" +
			"    synchronized (this) { \n" +
			"      if (mu == null) { \n" +
			"	u = 5; \n" +
			"	synchronized (nu) { \n" +
			"	  int i = w; \n" +
			"	  w = i + 1; \n" +
			"	} \n" +
			"      } else { \n" +
			"	synchronized (mu) { \n" +
			"	  int i = w; \n" +
			"	  w = i + 1; // fails \n" +
			"	} \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  int m7() { \n" +
			"    return u;  // fails \n" +
			"  } \n" +
			" \n" +
			"  void m8() { \n" +
			"    u = 8;  // fails \n" +
			"  } \n" +
			" \n" +
			"  int m9() { \n" +
			"    if (mu == null) { \n" +
			"      return w;  // fails \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this; \n" +
			"  void m10() { \n" +
			"    if (mu != null) { \n" +
			"      synchronized (mu) { \n" +
			"	v = 4;  // fails \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\max(\\lockset) < this; \n" +
			"  int m11() { \n" +
			"    if (mu != null) { \n" +
			"      synchronized (mu) { \n" +
			"	return v;  // fails \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m12() { \n" +
			"    //@ assert \\lockset[\\max(\\lockset)]; \n" +
			"    //@ assert null <= \\max(\\lockset); \n" +
			"    //@ assert \\lockset[null]; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires mu0 < mu1 && mu1 < mu2; \n" +
			"  //@ requires nu0 <= nu1 && nu1 <= nu2; \n" +
			"  //@ requires pu0 <= pu1 && pu1 < pu2; \n" +
			"  //@ requires qu0 < qu1 && qu1 <= qu2; \n" +
			"  void m13Transitivity(Object mu0, Object mu1, Object mu2, \n" +
			"		       Object nu0, Object nu1, Object nu2, \n" +
			"		       Object pu0, Object pu1, Object pu2, \n" +
			"		       Object qu0, Object qu1, Object qu2) { \n" +
			"    //@ assert mu0 <= mu2; \n" +
			"    //@ assert mu0 < mu2; \n" +
			"    //@ assert nu0 <= nu2; \n" +
			"    //@ assert pu0 <= pu2; \n" +
			"    //@ assert pu0 < pu2; \n" +
			"    //@ assert qu0 < qu2; \n" +
			"    //@ assert qu0 <= qu2; \n" +
			"  } \n" +
			" \n" +
			"  void m14(Object mu, int k) { \n" +
			"    switch (k) { \n" +
			"      case 0: \n" +
			"	//@ assert null <= mu; \n" +
			"	break; \n" +
			"      case 1: \n" +
			"	//@ assume \\lockset[mu]; \n" +
			"	//@ assert null <= mu; \n" +
			"	break; \n" +
			"      case 2: \n" +
			"	//@ assume \\lockset[mu]; \n" +
			"	//@ assert mu <= \\max(\\lockset); \n" +
			"	break; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_128() {
			this.runNegativeTest(new String[] {
			testsPath + "SyncConstructor.java", 
			"class SyncConstructor { \n" +
			" \n" +
			"  /*@ non_null */ Object mu = new Object(); \n" +
			"  static /*@ non_null */ Object nu = new Object(); \n" +
			" \n" +
			"  /*@ monitored */ int x; \n" +
			"  /*@ monitored_by mu; */ int y; \n" +
			"  /*@ monitored_by nu; */ static int g; \n" +
			" \n" +
			"  // ----------  WRITE ACCESS  ---------- \n" +
			" \n" +
			"  SyncConstructor(/*@ non_null */ SyncConstructor that) { \n" +
			"    x = 5;  // no race, because accessor is this \n" +
			"    that.x = 5;  // race, since this != that \n" +
			" \n" +
			"    SyncConstructor o = this; \n" +
			"    o.y = 6;  // no race \n" +
			"    o = that; \n" +
			"    o.y = 5;  // race \n" +
			" \n" +
			"    g = 5;  // race, because the special rule applies only to instance fields \n" +
			"  } \n" +
			" \n" +
			"  SyncConstructor() { \n" +
			"    this.g = 5;  // race (the \"this\" is irrelevant to static fields) \n" +
			"  } \n" +
			" \n" +
			"  void m(/*@ non_null */ SyncConstructor that) { \n" +
			"    x = 5;       // race \n" +
			"    that.x = 5;  // race \n" +
			" \n" +
			"    SyncConstructor o = this; \n" +
			"    o.y = 6;  // race \n" +
			"    o = that; \n" +
			"    o.y = 5;  // race \n" +
			" \n" +
			"    g = 5;  // race \n" +
			"  } \n" +
			" \n" +
			"  // ----------  READ ACCESS  ---------- \n" +
			" \n" +
			"  SyncConstructor(/*@ non_null */ SyncConstructor that, int q) { \n" +
			"    int k; \n" +
			"    k = x;  // no race, because accessor is this \n" +
			"    k = that.x;  // race, since this != that \n" +
			" \n" +
			"    SyncConstructor o = this; \n" +
			"    k = o.y+1;  // no race \n" +
			"    o = that; \n" +
			"    k = o.y;  // race \n" +
			" \n" +
			"    k = g;  // race, because the special rule applies only to instance fields \n" +
			"  } \n" +
			" \n" +
			"  SyncConstructor(int q) { \n" +
			"    int k; \n" +
			"    k = this.g;  // race (the \"this\" is irrelevant to static fields) \n" +
			"  } \n" +
			" \n" +
			"  void m(/*@ non_null */ SyncConstructor that, int q) { \n" +
			"    int k; \n" +
			"    k = x;       // race \n" +
			"    k = that.x;  // race \n" +
			" \n" +
			"    SyncConstructor o = this; \n" +
			"    k = o.y+1;  // race \n" +
			"    o = that; \n" +
			"    k = o.y;  // race \n" +
			" \n" +
			"    k = g;  // race \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_129() {
			this.runNegativeTest(new String[] {
			testsPath + "trycatch.java", 
			"class Try { \n" +
			"  void m1() { \n" +
			"    int x,y; \n" +
			"    T2 t; \n" +
			"    try { \n" +
			"      x=0; \n" +
			"      //@ assume \\typeof(t) == \\type(T2) && t != null; \n" +
			"      throw t; \n" +
			"    } catch(T3 t3) { \n" +
			"      x=3; \n" +
			"    } catch(T1 t1) { \n" +
			"      x=1; \n" +
			"    } catch(T2 t2) { \n" +
			"      x=2; \n" +
			"    } \n" +
			"    //@ assert x==1; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_130() {
			this.runNegativeTest(new String[] {
			testsPath + "trycatch.java", 
			"class T1 extends Throwable {} \n" 
			}, "ERROR");
			}

			public void test_131() {
			this.runNegativeTest(new String[] {
			testsPath + "trycatch.java", 
			"class T2 extends T1 {} \n" 
			}, "ERROR");
			}

			public void test_132() {
			this.runNegativeTest(new String[] {
			testsPath + "trycatch.java", 
			"class T3 extends T2 {} \n" 
			}, "ERROR");
			}

			public void test_133() {
			this.runNegativeTest(new String[] {
			testsPath + "unreachable.java", 
			" \n" +
			"class unreachable { \n" +
			"  void m1() { \n" +
			"    if (true) { \n" +
			"    } else { \n" +
			"      //@ unreachable; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_134() {
			this.runNegativeTest(new String[] {
			testsPath + "switch.java", 
			"class Switch { \n" +
			"  //@ requires p == 3; \n" +
			"  void m0(int p) { \n" +
			"    int x=0; \n" +
			"    switch(p) { \n" +
			"      case 2: \n" +
			"	x=2; \n" +
			"	break; \n" +
			"      case 3: \n" +
			"	x=3; \n" +
			"	break; \n" +
			"      default: \n" +
			"	x=5; \n" +
			"    } \n" +
			"    //@ assert x==3; \n" +
			"  } \n" +
			" \n" +
			"  void m1() { \n" +
			"    int x=0; \n" +
			"    switch(2+1) { \n" +
			"      case 2: \n" +
			"	x=2; \n" +
			"	break; \n" +
			"      case 3: \n" +
			"	x=3; \n" +
			"	break; \n" +
			"      default: \n" +
			"	x=5; \n" +
			"    } \n" +
			"    //@ assert x==3; \n" +
			"  } \n" +
			" \n" +
			"  void m2() { \n" +
			"    int x=0; \n" +
			"    switch(5) { \n" +
			"      case 2: \n" +
			"	x=2; \n" +
			"	break; \n" +
			"      default: \n" +
			"	x=5; \n" +
			"    } \n" +
			"    //@ assert x==5; \n" +
			"  } \n" +
			" \n" +
			"  void m3() { \n" +
			"    int x=0; \n" +
			"    switch(6) { \n" +
			"      case 2: \n" +
			"	x=2; \n" +
			"	break; \n" +
			"    } \n" +
			"    //@ assert x==0; \n" +
			"  } \n" +
			" \n" +
			"  void m4() { \n" +
			"    int x=0; \n" +
			"    switch(6) { \n" +
			"      case 2: \n" +
			"	x=2; \n" +
			"	break; \n" +
			"    } \n" +
			"    // The following should fail: \n" +
			"    //@ assert x==2; \n" +
			"  } \n" +
			" \n" +
			"  void m5(int y) { \n" +
			"    int x=0; \n" +
			"    switch(y) { \n" +
			"      case 2: \n" +
			"	x=2; \n" +
			"	break; \n" +
			"    } \n" +
			"    // The following should fail: \n" +
			"    //@ assert x==0; \n" +
			"  } \n" +
			" \n" +
			"  void m6(int y) { \n" +
			"    int x=0; \n" +
			"    switch(y) { \n" +
			"      case 2: \n" +
			"	x=2; \n" +
			"	break; \n" +
			"    } \n" +
			"    // The following should fail: \n" +
			"    //@ assert x==2; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_135() {
			this.runNegativeTest(new String[] {
			testsPath + "try.java", 
			"class TryFinally { \n" +
			"  void m() { \n" +
			"    int x,y; \n" +
			"    try { \n" +
			"      x=1; \n" +
			"    } finally { \n" +
			"      x=2; \n" +
			"    } \n" +
			"    //@ assert x==2; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_136() {
			this.runNegativeTest(new String[] {
			testsPath + "Neg.java", 
			"class Neg { \n" +
			" \n" +
			"    //@ invariant \\nonnullelements(names); \n" +
			"    String[] names = new String[0]; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_137() {
			this.runNegativeTest(new String[] {
			testsPath + "Neg.java", 
			"class Neg2 { \n" +
			" \n" +
			"    //@ invariant foos != null; \n" +
			"    //@ invariant foos.length>1; \n" +
			"    String[] foos = new String[10]; \n" +
			" \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_138() {
			this.runNegativeTest(new String[] {
			testsPath + "Neg.java", 
			"class NegUser { \n" +
			" \n" +
			"    //@ requires X != null; \n" +
			"    //@ requires Y != null; \n" +
			"    void foo(Neg X, Neg2 Y) { \n" +
			"	Y.foos[0] = null; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_139() {
			this.runNegativeTest(new String[] {
			testsPath + "NonNull.java", 
			"/** This file contains some tests that the \"non_null\" pragma generates \n" +
			" ** appropriate assumptions. \n" +
			" **/ \n" +
			" \n" +
			"class NonNull { \n" +
			"  // the following would generate a compile-time error \n" +
			"  // /*@ non_null */ int x; \n" +
			"   \n" +
			"  /*@ non_null */ Object o; \n" +
			"   \n" +
			"  // without the initializer, the following would generate a compile-time error \n" +
			"  static Object p = new NonNull() /*@ non_null */; \n" +
			" \n" +
			"  //@ ensures \\result != null; \n" +
			"  Object m(int k, Object x, /*@ non_null */ Object y, \n" +
			"	   /*@ non_null */ Object z) { \n" +
			"    if (x != null) \n" +
			"      return x; \n" +
			"    else if (k == 0) \n" +
			"      return y; \n" +
			"    else if (k == 1) \n" +
			"      return z; \n" +
			"    else if (k == 2) \n" +
			"      return o; \n" +
			"    else \n" +
			"      return p; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_140() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusNowarns.java", 
			"class BogusNowarns { \n" +
			"  //@ nowarn Null, Bogus, Exception \n" +
			"  //@ nowarn Bogus; \n" +
			"  //@ nowarn Bogus, Bogus, Bogus \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_141() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusAssignments.java", 
			"class BogusAssignments { \n" +
			"  final int x = 5; \n" +
			"  void m() { \n" +
			"    x = 3;  // this is a \"final\" field, but we don't currently disallow them \n" +
			"  } \n" +
			"   \n" +
			"  void n() { \n" +
			"    int[] a = null; \n" +
			"    a.length = 3; \n" +
			"  } \n" +
			"   \n" +
			"  //@ modifies a.length; \n" +
			"  //@ modifies x; \n" +
			"  void p(int[] a) { \n" +
			"  } \n" +
			"   \n" +
			"  void q() { \n" +
			"    int[] a = null; \n" +
			"    p(a); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_142() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusGhost.java", 
			" \n" +
			"class BogusGhost { \n" +
			"  //@ ghost public int a = 5 \n" +
			"  //@ ghost int b \n" +
			"  //@ ghost protected int c \n" +
			"  //@ ghost public int[][] d[][]; \n" +
			"  //@ ghost public static int e; \n" +
			"  //@ ghost static public int f; \n" +
			"  //@ ghost final public int g; \n" +
			"  //@ ghost static final public int h; \n" +
			"  //@ ghost public \\TYPE i; \n" +
			"  /*@ ghost public \\TYPE [] [ ] j [] [][ ]; */ \n" +
			"  //@ ghost public BogusGhost k; \n" +
			"  //@ ghost public int l; \n" +
			"  //@ ghost static public int l; \n" +
			"  int m; \n" +
			"  //@ ghost public int m; \n" +
			"  int n; \n" +
			"  //@ ghost public static int n; \n" +
			"  static int o; \n" +
			"  //@ ghost public int o; \n" +
			"  static int p; \n" +
			"  //@ ghost public static int p; \n" +
			"  //@ ghost public int ghost; \n" +
			"   \n" +
			"  //@ invariant k != null; \n" +
			" \n" +
			"  //@ ghost public int x; \n" +
			"} \n" +
			" \n" +
			"interface BogusGhostInterfaceA { \n" +
			"  //@ ghost public int x; \n" +
			"} \n" +
			" \n" +
			"interface BogusGhostInterfaceB { \n" +
			"  //@ ghost public int x; \n" +
			"} \n" +
			" \n" +
			"interface BogusGhostInterfaceC extends BogusGhostInterfaceA, BogusGhostInterfaceB { \n" +
			"  //@ ghost public int x; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_143() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusGhost.java", 
			"class BogusGhostSub extends BogusGhost { \n" +
			"  //@ ghost public int x; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_144() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusGhost.java", 
			"class BogusGhostSubSubA extends BogusGhostSub implements BogusGhostInterfaceA, BogusGhostInterfaceB { \n" +
			"  //@ ghost public int x; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_145() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusGhost.java", 
			"class BogusGhostSubSubB extends BogusGhostSub implements BogusGhostInterfaceA, BogusGhostInterfaceB { \n" +
			"  //@ ghost public int x; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_146() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusGhost.java", 
			"class BogusGhostX extends BogusGhostSub implements BogusGhostInterfaceA, BogusGhostInterfaceC { \n" +
			"  //@ ghost public int x; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_147() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusGhost.java", 
			"class BogusGhostXX extends BogusGhostX { \n" +
			"  //@ ghost public int x; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_148() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusGhost.java", 
			"class BogusGhostXXX extends BogusGhostXX implements BogusGhostInterfaceB { \n" +
			"  int x; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_149() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusGhost.java", 
			"class GhostSet { \n" +
			"  //@ ghost public static int x; \n" +
			"  //@ ghost public int y; \n" +
			"  //@ ghost public \\TYPE t; \n" +
			"  //@ ghost public double[] d; \n" +
			"   \n" +
			"  void m0() { \n" +
			"    // The following two \"set\" pragmas are legal \n" +
			"    //@ set x = 0 \n" +
			"    //@ set y = 0 \n" +
			"  } \n" +
			" \n" +
			"  static void m1() { \n" +
			"    /*@ set x = 0; */  // legal \n" +
			"    /*@ set y = 0; */   // not legal \n" +
			"  } \n" +
			" \n" +
			"  //@ modifies t \n" +
			"  //@ ensures \\old(t == \\type(int)) ==> t == \\type(double); \n" +
			"  void m2() { \n" +
			"    //@ set t = \\type(GhostSet); \n" +
			"    //@ set t = \\type(int[]); \n" +
			"    //@ set t = \\type(\\TYPE); \n" +
			"    //@ set t = \\type(\\TYPE[]); \n" +
			"    //@ set t = \\type(double); \n" +
			"  } \n" +
			" \n" +
			"  int z; \n" +
			"  //@ ghost public int[] w; \n" +
			"   \n" +
			"  int m3() { \n" +
			"    /*@ set z = 5; */            // not legal \n" +
			"    /*@ set w = new int[10]; */  // not legal \n" +
			"    /*@ set w[z] = 3; */         // not legal \n" +
			"  } \n" +
			" \n" +
			"  //@ ghost public boolean bo; \n" +
			"  void m4() { \n" +
			"    /*@ set bo = (\\forall int i; i < i+1); */ \n" +
			"    /*@ set bo = (\\exists int i; i*i < 0); */ \n" +
			"    /*@ set bo = (\\lblneg Hello 1 < 2); */ \n" +
			"    /*@ set bo = (\\lblpos Hello 1 < 2); */ \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_150() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse4.java", 
			"class WontEvenParse4 { \n" +
			"  //@ ensures true; \n" +
			"  //@ ensures \\result == (3 < 4 ? new Object() : new int[12]); \n" +
			"  Object m4() { \n" +
			"    return 3 < 4 ? new Object() : new int[12]; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (new Object()) != null; \n" +
			"  Object m3() {} \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_151() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusLoops.java", 
			"class BogusLoops { \n" +
			"  int loopinvs(int x) { \n" +
			"    int y = 3; \n" +
			"    int[] a = new int[10]; \n" +
			" \n" +
			"    //@ loop_invariant x < x+2 \n" +
			"    //@ loop_invariant y == y \n" +
			"    while (x++ < y) { \n" +
			"      //@ assert 0 < x \n" +
			"      //@ unreachable \n" +
			"      //@ assume 0 < y \n" +
			"      // Loop invariants cannot be placed here: \n" +
			"      //@ loop_invariant a != null \n" +
			"      //@ loop_invariant \\old(x) <= x; \n" +
			"      a[0] = y; \n" +
			"      // A loop invariant cannot be placed here: \n" +
			"      //@ loop_invariant a[0] == 0; \n" +
			"    } \n" +
			" \n" +
			"    //@ loop_invariant x < x+2; \n" +
			"    //@ loop_invariant y == y; \n" +
			"    do { \n" +
			"      //@ assert 0 < x \n" +
			"      //@ unreachable \n" +
			"      //@ assume 0 < y \n" +
			"      // Loop invariants cannot be placed here: \n" +
			"      //@ loop_invariant a != null; \n" +
			"      //@ loop_invariant \\old(x) <= x; \n" +
			"      a[0] = y; \n" +
			"      // A loop invariant cannot be placed here: \n" +
			"      //@ loop_invariant a[0] == 1; \n" +
			"    } while (x++ < y); \n" +
			"     \n" +
			"    //@ loop_invariant x < x+2; \n" +
			"    //@ loop_invariant y == y; \n" +
			"    for (int i = loopinvs(10); i < 20; i++) { \n" +
			"      //@ assert 0 < x \n" +
			"      //@ unreachable \n" +
			"      //@ assume 0 < y \n" +
			"      // Loop invariants cannot be placed here: \n" +
			"      //@ loop_invariant a != null; \n" +
			"      //@ loop_invariant \\old(x) <= x; \n" +
			"      a[0] = y; \n" +
			"      // A loop invariant cannot be placed here: \n" +
			"      //@ loop_invariant a[0] == 2; \n" +
			"    } \n" +
			" \n" +
			"    while (x++ < y) { \n" +
			"    } \n" +
			"    //@ loop_invariant a[0] == 3; \n" +
			" \n" +
			"    //@ loop_invariant 2 < y; \n" +
			"    while (x++ < y) { \n" +
			"      a[1] = x; \n" +
			"      //@ loop_invariant 3 < y; \n" +
			"      //@ loop_invariant 4 < y; \n" +
			"      do { \n" +
			"	//@ loop_invariant 5 < y; \n" +
			"	for (x++, y++; y < 20; x++, y++) { \n" +
			"	  {} \n" +
			"	  //@ loop_invariant a[0] == 4; \n" +
			"	} \n" +
			"      } while (x++ < y); \n" +
			"    } \n" +
			"     \n" +
			"    while (false) \n" +
			"      ; \n" +
			"    //@ loop_invariant a[0] == 5; \n" +
			" \n" +
			"    while (x++ < y) { \n" +
			"      ; \n" +
			"      //@ loop_invariant a[0] == 6; \n" +
			"    } \n" +
			" \n" +
			"     \n" +
			"    while (x++ < y) { \n" +
			"      MyLabel: { //@ loop_invariant a[0] == 7; \n" +
			"      } \n" +
			"      //@ loop_invariant a[0] == 8; \n" +
			"    } \n" +
			" \n" +
			"    //@ loop_invariant a[0] == 9; \n" +
			"    while (x++ < y) { \n" +
			"      int z = 0; \n" +
			"    } \n" +
			"     \n" +
			"    //@ loop_invariant a[0] == 10; \n" +
			"    while (x++ < y) { \n" +
			"      int z; \n" +
			"    } \n" +
			"     \n" +
			"    return 0; \n" +
			"  } \n" +
			" \n" +
			"  void goodLoops(int x) { \n" +
			"    int y = 0; \n" +
			"    int[] a = new int[20]; \n" +
			"    //@ loop_invariant \\lockset == \\lockset; \n" +
			"    //@ loop_invariant \\fresh(a) ==> \\old(x+y) == x+y; \n" +
			"    while (x++ < y) { \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_152() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusModifiers.java", 
			"class BogusModifiers { \n" +
			"  void good(int t) { \n" +
			"    final int x = 3; \n" +
			"    for (final int i = 0; i < 100; ) { \n" +
			"    } \n" +
			"    for (/*@ non_null */ BogusModifiers nf = null; t < 10; t++) { \n" +
			"    } \n" +
			"    for (final /*@ non_null */ BogusModifiers nf = null; t < 20; t++) { \n" +
			"    } \n" +
			"    for (/*@ non_null */ final BogusModifiers nf = null; t < 30; t++) { \n" +
			"    } \n" +
			"    for (/*@ readable_if 30 <= t; */ BogusModifiers nf = null; t < 30; t++) { \n" +
			"      Object o = nf; \n" +
			"    } \n" +
			"    for (/*@ readable_if 30 <= t; */ BogusModifiers nf = null; t < 30; t++) { \n" +
			"      Object o = nf; \n" +
			"    } \n" +
			"    for (BogusModifiers nf = null, xf = null /*@ readable_if 30 <= t; */; t < 30; t++) { \n" +
			"      Object o = nf; \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  abstract native int xx = 0; \n" +
			" \n" +
			"  void m0() { \n" +
			"    public int x0 = 0; \n" +
			"    private int x1 = 0; \n" +
			"    protected int x2 = 0; \n" +
			"    static int x3 = 0; \n" +
			"    final int x4 = 0;  // this one is fine for local variables \n" +
			"    // Although \"synchronized\" is a modifier, the Javafe parser does not expect \n" +
			"    // it to be a modifier in this context, so it tries to parse the following \n" +
			"    // as a statement, which generates a parsing error: \n" +
			"    // synchronized int x5 = 0; \n" +
			"    volatile int x6 = 0; \n" +
			"    transient int x7 = 0; \n" +
			"    native int x8 = 0; \n" +
			"    abstract int x9 = 0; \n" +
			"  } \n" +
			"   \n" +
			"  void m1() { \n" +
			"    /*@ spec_public */ int x0 = 0; \n" +
			"    /*@ non_null */ int x1 = 0; \n" +
			"    /*@ requires true; */ int x2 = 0; \n" +
			"    /*@ modifies x0 */ int x3 = 0; \n" +
			"    /*@ ensures true; */ int x4 = 0; \n" +
			"    /*@ exsures (Throwable t) true; */ int x5 = 0; \n" +
			"    int x6 = 0 /*@ exsures (Throwable t) true */; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_153() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse5.java", 
			"class WontEvenParse5 { \n" +
			"  void m5(Object[] a) { \n" +
			"    //@ assert WontEvenParse5.\\nonnullelements(a); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_154() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse1.java", 
			"class WontEvenParse1 { \n" +
			"  boolean m1() { \n" +
			"    //@ assert m1(); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_155() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse3.java", 
			"class WontEvenParse3 { \n" +
			"  void m3() { \n" +
			"    //@ assert new int[10]; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_156() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse8.java", 
			"class WontEvenParse8 { \n" +
			"  //@ exsures (Throwable a[]) true; \n" +
			"  void m() { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_157() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusInput.java", 
			"// This class contains many errors that the type checker should catch \n" +
			"// The tests are designed to pass the parser, but many fail the type checker. \n" +
			" \n" +
			"/*@ uninitialized */ \n" +
			"/*@ non_null */ \n" +
			"/*@ readable_if x == 5 */ \n" +
			"/*@ writable_if x == 5 */ \n" +
			"/*@ monitored_by null, true */ \n" +
			"/*@ monitored */ \n" +
			"class BogusInput { \n" +
			"  //@ axiom this != null \n" +
			"   \n" +
			"  /*@ readable_if this != null */  // this is allowed \n" +
			"  /*@ writable_if this != null */  // this is allowed \n" +
			"  int x; \n" +
			"  //@ axiom x == 5 \n" +
			" \n" +
			"  //@ readable_if x < 10 \n" +
			"  //@ writable_if x < 10 \n" +
			"  static int g; \n" +
			"  /*@ axiom g == 12 */  // this is allowed \n" +
			" \n" +
			"  //@ axiom \\lockset == \\lockset \n" +
			"  //@ invariant \\lockset == \\lockset \n" +
			"  //@ axiom \\max(\\lockset) == null; \n" +
			"  //@ invariant \\max(\\lockset) == null \n" +
			" \n" +
			"  //@ axiom \\result == \\result; \n" +
			"  //@ invariant \\result == \\result \n" +
			" \n" +
			"  //@ axiom \\old(x) == x && (\\forall BogusInput t; t.x == t.x); \n" +
			"  //@ invariant \\old(x) == x && (\\forall BogusInput t; t.x == t.x); \n" +
			"   \n" +
			"  //@ requires \\result == \\result \n" +
			"  //@ modifies a[ (\\result == \\result ? 0 : 1 )] \n" +
			"  //@ ensures \\result == \\result \n" +
			"  BogusInput(int[] a) { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\result == 0 \n" +
			"  //@ modifies a[\\result] \n" +
			"  //@ ensures \\result == 0 \n" +
			"  int m(int[] a) { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\result == 0 \n" +
			"  //@ modifies a[\\result] \n" +
			"  //@ ensures \\result == 0 \n" +
			"  //@ also modifies a[\\result] \n" +
			"  //@ also ensures \\result == 0; \n" +
			"  int notAMethod; \n" +
			"   \n" +
			"  /*@ uninitialized */ int uninitA; \n" +
			"  /*@ uninitialized */ int uninitB = 5; \n" +
			"  /*@ uninitialized */ static int uninitC; \n" +
			"  /*@ uninitialized */ static int uninitD = 5; \n" +
			"  /*@ uninitialized */ int uninitE, uninitF; \n" +
			"  /*@ uninitialized */ int uninitM() { return 0; } \n" +
			"  void uninit(/*@ uninitialized */ int p) { \n" +
			"    /*@ uninitialized */ int a; \n" +
			"    /*@ uninitialized */ int b = 0; \n" +
			"    /*@ uninitialized */ int c = 0, d; \n" +
			"    /*@ uninitialized */ int e = 0, f = 0; \n" +
			"     \n" +
			"    // The following are from ESCJ 17: \n" +
			"    /*@ uninitialized */ Object x = null, y = new Object(); \n" +
			"    /*@ uninitialized */ Object w, z = null; \n" +
			"    /*@ uninitialized */ Object v; \n" +
			"  } \n" +
			" \n" +
			"  /*@ non_null */ int nn0; \n" +
			"  int nn1 /*@ non_null */; \n" +
			"  /*@ non_null */ Object nn2; \n" +
			"  Object nn3 /*@ non_null */; \n" +
			"  /*@ non_null */ Cloneable nn4; \n" +
			"  /*@ non_null */ int[] nn5, nn6; \n" +
			"  /*@ non_null */ int nn7[], nn8; \n" +
			"  /*@ non_null */ static int nn9; \n" +
			"  /*@ non_null */ static BogusInput nn10; \n" +
			"  /*@ non_null */ static BogusInput nn11 = null;  // ironically, the type checker allows this one \n" +
			"  /*@ non_null */ static BogusInput nn12 = new BogusInput(null); \n" +
			"  /*@ non_null */ static BogusInput nn13, n14 = new BogusInput(null), n15; \n" +
			"  /*@ non_null */ /*@ non_null */ /*@ non_null non_null */ Object n16; \n" +
			"  /*@ non_null */ Object nonNullM() { return null; } \n" +
			"  void nonNull(/*@ non_null */ int p, int q, /*@ non_null */ Object r) { \n" +
			"    /*@ non_null */ int a; \n" +
			"    /*@ non_null */ Object b; \n" +
			"    /*@ non_null */ Object c = null; \n" +
			"    /*@ non_null */ Object d = null, e = new Object(), f; \n" +
			"    Object g = null, h = new Object(), i /*@ non_null */ ; \n" +
			"    /*@ non_null */ int[] j; \n" +
			"    int[] k /*@ non_null */; \n" +
			"    /*@ non_null */ int l[]; \n" +
			"    int m[] /*@ non_null */; \n" +
			"    /*@ uninitialized non_null */ int[] n = null; \n" +
			"  } \n" +
			" \n" +
			"  /*@ readable_if true; */ int defif0; \n" +
			"  /*@ readable_if defif0 == defif1; */ int defif1; \n" +
			"  /*@ readable_if true; */ static int defif2; \n" +
			"  /*@ readable_if defif0 == defif3; */ static int defif3; \n" +
			"  /*@ readable_if defif4 || defif5; */ boolean defif4, defif5;  // this is allowed \n" +
			"  /*@ readable_if true; */ int definedifM() { return 0; } \n" +
			"  void definedIf0(/*@ readable_if true; */ int x) { \n" +
			"    /*@ readable_if true; */ int a; \n" +
			"    /*@ readable_if a == 2; */ int b; \n" +
			"    /*@ readable_if 0 <= c; */ int c; \n" +
			"    /*@ readable_if a == 2; */ int d = 5; \n" +
			"    /*@ readable_if this == null || defif0 == defif2; */ int e; \n" +
			"  } \n" +
			"  static void definedIf1() { \n" +
			"    /*@ readable_if this == null || defif0 == defif2; */ int e; \n" +
			"  } \n" +
			" \n" +
			"  void definedIf2() { \n" +
			"    /*@ readable_if defif0 == 3; */ boolean defif0;  // this is fine \n" +
			"    /*@ readable_if a; */ boolean a;  // this is not fine \n" +
			"    /*@ readable_if a; */ boolean x, y;  // this is fine \n" +
			"    /*@ readable_if c; */ boolean b, c, d;  // this is not fine, for any of the variables \n" +
			"  } \n" +
			"   \n" +
			"  Object[] mus; \n" +
			"  /*@ monitored_by mus[0], this, undeclaredVariable, this.mus[1]; monitored_by mb0 */ int mb0; \n" +
			"  /*@ monitored_by mus, this, this.mus */ static int mb1; \n" +
			"  /*@ monitored_by mus */ void monitoredBy0(/*@ monitored_by this */ int p) { \n" +
			"    /*@ monitored_by this */ int x; \n" +
			"  } \n" +
			"  /*@ monitored_by mb1 */ static void monitoredBy1(/*@ monitored_by mb1 */ int p) { \n" +
			"    /*@ monitored_by mb1 */ int x; \n" +
			"    /*@ monitored_by this */ int y; \n" +
			"  } \n" +
			" \n" +
			"  /*@ monitored */ int mo0; \n" +
			"  /*@ monitored monitored */ /*@ monitored */ /*@ monitored_by this */ int mo1 /*@ monitored */; \n" +
			"  /*@ monitored */ static int mo2; \n" +
			"  /*@ monitored */ void monitored0(/*@ monitored */ int p) { \n" +
			"    /*@ monitored */ int x; \n" +
			"  } \n" +
			"  /*@ monitored */ static void monitored1(/*@ monitored */ int p) { \n" +
			"    /*@ monitored */ int x; \n" +
			"  } \n" +
			" \n" +
			"  static void pp() { \n" +
			"    this.pp();  // \"this\" is not allowed in this context \n" +
			"  } \n" +
			" \n" +
			"  int[] iarr; \n" +
			"  //@ requires mus[*] == null; \n" +
			"  //@ modifies mus[*]; \n" +
			"  //@ modifies iarr[iarr[*]]; \n" +
			"  //@ ensures mus[*] == null; \n" +
			"  void wildRef() { \n" +
			"  } \n" +
			" \n" +
			"  static int xx; \n" +
			"  //@ axiom new Object(blah); \n" +
			"  //@ axiom new int[5]; \n" +
			"  //@ axiom (xx = 0) == 0; \n" +
			"  //@ axiom (xx *= 0) == 0; \n" +
			"  //@ axiom (xx /= 0) == 0; \n" +
			"  //@ axiom (xx %= 0) == 0; \n" +
			"  //@ axiom (xx += 0) == 0; \n" +
			"  //@ axiom (xx -= 0) == 0; \n" +
			"  //@ axiom (xx <<= 0) == 0; \n" +
			"  //@ axiom (xx >>= 0) == 0; \n" +
			"  //@ axiom (xx >>>= 0) == 0; \n" +
			"  //@ axiom (xx &= 0) == 0; \n" +
			"  //@ axiom (xx |= 0) == 0; \n" +
			"  //@ axiom (xx ^= 0) == 0; \n" +
			"  //@ axiom (++xx) == 0; \n" +
			"  //@ axiom (xx++) == 0; \n" +
			"  //@ axiom (--xx) == 0; \n" +
			"  //@ axiom (xx--) == 0; \n" +
			" \n" +
			"  void mPredicates() { \n" +
			"    // These are okay \n" +
			"    /*@ assert (\\forall int i; i < i+1); */ \n" +
			"    /*@ assert (\\exists int i; i*i < 0); */ \n" +
			"    /*@ assert (\\lblneg Hello 1 < 2); */ \n" +
			"    /*@ assert (\\lblpos Hello 1 < 2); */ \n" +
			"     \n" +
			"    // Argument to cast cannot be a predicate \n" +
			"    /*@ assert (boolean)(\\forall int i; i < i+1); */ \n" +
			"    /*@ assert (boolean)(\\exists int i; i*i < 0); */ \n" +
			"    /*@ assert (boolean)(\\lblneg Hello 1 < 2); */ \n" +
			"    /*@ assert (boolean)(\\lblpos Hello 1 < 2); */ \n" +
			"     \n" +
			"    // Arguments to ? : cannot be predicates \n" +
			"    /*@ assert (\\forall int i; i < i+1) ? (\\forall int i; i < i+1) : (\\forall int i; i < i+1); */ \n" +
			"    /*@ assert (\\exists int i; i*i < 0) ? (\\exists int i; i*i < 0) : (\\exists int i; i*i < 0); */ \n" +
			"    /*@ assert (\\lblneg Hello 1 < 2) ? (\\lblneg Hello 1 < 2) : (\\lblneg Hello 1 < 2); */ \n" +
			"    /*@ assert (\\lblpos Hello 1 < 2) ? (\\lblpos Hello 1 < 2) : (\\lblpos Hello 1 < 2); */ \n" +
			" \n" +
			"    // These are okay \n" +
			"    int xyz = 0; \n" +
			"    /*@ assert (\\forall int i; i < 0 ? i < i*i : i <= i*i); */ \n" +
			"    /*@ assert (\\exists int i; i < 0 ? false : i == i*i); */ \n" +
			"    /*@ assert (\\lblneg MyLabel xyz == 0); */ \n" +
			"    /*@ assert (\\lblpos MyLabel xyz == 0); */ \n" +
			" \n" +
			"    // Name clashes \n" +
			"    /*@ assume (\\forall int i; (\\forall int i; i == i)); */ \n" +
			"    /*@ assume (\\forall int i; (\\forall Object j; (\\exists double i; i == i))); */ \n" +
			"    /*@ assume (\\forall int i, i; (\\forall Object j; (\\exists double i; i == i))); */ \n" +
			"    /*@ assume (\\forall int i, j; (\\forall Object j; (\\exists double i; i == i))); */ \n" +
			"    /*@ assume (\\forall char xyz; xyz == xyz); */ \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_158() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse7.java", 
			"class WontEvenParse7 { \n" +
			"  void m() { \n" +
			"    //@ assert \\type(WontEvenParse7[]) <: \\type(m); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_159() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse0.java", 
			"class WontEvenParse0 { \n" +
			"  //@ ghost public int x; \n" +
			"  int m0() { \n" +
			"    //@ set x = m0(); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_160() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusSpec.java", 
			"class BogusSpec { \n" +
			"  //@ ensures \\result < 6; \n" +
			"  //@ ensures \\result == \\result; \n" +
			"  //@ ensures \\result != \\result; \n" +
			"  //@ ensures \\result <= \\result; \n" +
			"  void m0() { \n" +
			"  } \n" +
			" \n" +
			"  Object x; \n" +
			"  //@ requires x == 6; \n" +
			"  //@ modifies this != null; \n" +
			"  //@ modifies this.x, x \n" +
			"  //@ ensures this.x == null || \\fresh(this.x); \n" +
			"  //@ ensures \\result < x; \n" +
			"  int m1(int x) { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\result; \n" +
			"  //@ modifies \\result \n" +
			"  //@ ensures \\result; \n" +
			"  boolean m2() { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires true; \n" +
			"  //@ modifies x, x \n" +
			"  //@ also_modifies x, x \n" +
			"  //@ ensures x == null; \n" +
			"  //@ also_ensures x == null; \n" +
			"  //@ also modifies x, x; ensures x == null; \n" +
			"  void m3() { \n" +
			"  } \n" +
			"  //@ modifies a \n" +
			"  //@ requires 0 <= p && a != null; \n" +
			"  //@ modifies a[*], a, a[p] \n" +
			"  //@ ensures \\old(a[p]) == p ==> a[p+1] == p+1; \n" +
			"  void m4(int[] a, int p) { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x != null; \n" +
			"  //@ requires this != null; \n" +
			"  //@ modifies \\result.x; \n" +
			"  //@ modifies \\result, x; \n" +
			"  //@ ensures \\result == null; \n" +
			"  static Object m5() { \n" +
			"    return null; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\lockset == \\lockset; \n" +
			"  //@ requires \\lockset; \n" +
			"  //@ modifies \\lockset \n" +
			"  //@ ensures \\lockset == \\lockset; \n" +
			"  //@ ensures \\lockset; \n" +
			"  void m6() { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\old(x) == x; \n" +
			"  //@ requires \\old(\\old(x)) == x; \n" +
			"  //@ modifies x; \n" +
			"  //@ modifies \\old(this).x; \n" +
			"  //@ ensures \\old(x) == x; \n" +
			"  //@ ensures \\old(this) == null; \n" +
			"  //@ ensures \\old(x==x && \\old(this)==this); \n" +
			"  void m7() { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires \\fresh(x); \n" +
			"  //@ ensures \\fresh(x) == \\fresh(this); \n" +
			"  //@ ensures \\fresh(\\fresh(this) ? x : x); \n" +
			"  //@ ensures \\fresh(\\old(x)); \n" +
			"  //@ ensures \\old(\\fresh(x)); \n" +
			"  void m8() { \n" +
			"  } \n" +
			"   \n" +
			"  //@ requires x != null; \n" +
			"  //@ requires this != null; \n" +
			"  //@ requires \\result != null; \n" +
			"  //@ ensures \\result != null; \n" +
			"  //@ ensures this != null; \n" +
			"  //@ modifies \\result.x \n" +
			"  //@ modifies x, this.x; \n" +
			"  BogusSpec(int a) { \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result == null; \n" +
			"  //@ exsures (Throwable t) \\result == null \n" +
			"  //@ exsures (Throwable t) t == null \n" +
			"  //@ exsures (SomeException se) se == \\result \n" +
			"  //@ exsures (SomeException se) se == x && se == this; \n" +
			"  //@ also_exsures (Throwable t) t == null \n" +
			"  //@ exsures (Object o) true; exsures (int t) false; \n" +
			"  //@ exsures (Throwable x) true; \n" +
			"  //@ exsures (Throwable) true;  \n" +
			"  //@ exsures (java.lang.Throwable th) true; \n" +
			"  //@ exsures (java.lang.Throwable) true; \n" +
			"  //@ exsures (int) true; \n" +
			"  //@ exsures (Throwable j) true; \n" +
			"  //@ exsures (Throwable t) (\\forall Throwable t; t == t); \n" +
			"  //@ exsures (\\TYPE tt) tt == \\type(SomeException); \n" +
			"  //@ exsures (int[] a) a == a; \n" +
			"  //@ exsures (Cloneable c) true; \n" +
			"  Object m9(int j) throws Throwable { \n" +
			"    return null; \n" +
			"  } \n" +
			" \n" +
			"  //@ exsures (SomeException se) se != null; \n" +
			"  //@ exsures (Throwable t) t == 5; \n" +
			"  //@ exsures (SomeSubException sse) false; \n" +
			"  //@ exsures (SomeOtherException soe) soe != null; \n" +
			"  //@ exsures (RuntimeException rte) true; \n" +
			"  //@ exsures (ArrayStoreException ase) ase == ase; \n" +
			"  void m10() throws SomeException, NullPointerException, AnotherException { \n" +
			"  } \n" +
			"  //@ exsures (SomeException se) \\result == 2; \n" +
			"  //@ exsures (SomeException se) this != x; \n" +
			"  //@ also \n" +
			"  //@ exsures (SomeException se) true \n" +
			"  static int m11also() throws SomeException { \n" +
			"    return 4; \n" +
			"  } \n" +
			" \n" +
			"  //@ exsures (SomeException se) se == \\result && se == this && se == x; \n" +
			"  //@ exsures (Throwable tt) tt == se; \n" +
			"  //@ exsures (Throwable tt) d < 0.0; \n" +
			"  //@ exsures (SomeOtherException soe) true; \n" +
			"  //@ also_exsures (Throwable tt) true \n" +
			"  //@ also exsures (Throwable tt) true \n" +
			"  BogusSpec(double d) throws SomeException { \n" +
			"  } \n" +
			" \n" +
			"  //@ exsures (SomeException se) se == \\result && se == this && se == x; \n" +
			"  //@ exsures (Throwable tt) tt == se; \n" +
			"  //@ exsures (Throwable tt) d < 0.0; \n" +
			"  //@ exsures (SomeOtherException soe) true; \n" +
			"  //@ also exsures (Throwable tt) true \n" +
			"  BogusSpec(double d, double e) throws SomeException { \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_161() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusSpec.java", 
			"class BogusSpecSub extends BogusSpec { \n" +
			"  //@ requires true; \n" +
			"  //@ modifies x, x \n" +
			"  //@ also_modifies x, x \n" +
			"  //@ ensures x == null; \n" +
			"  //@ also_ensures x == null; \n" +
			"  //@ also modifies x, x; ensures x == null; \n" +
			"  void m3() { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires true; \n" +
			"  //@ modifies x, x \n" +
			"  //@ also modifies x, x; ensures x == null; \n" +
			"  void m3also() { \n" +
			"  } \n" +
			" \n" +
			"  //@ also_modifies \\lockset \n" +
			"  //@ also_ensures \\lockset == \\lockset; \n" +
			"  //@ also_ensures \\lockset; \n" +
			"  //@ also modifies \\lockset; ensures \\lockset == \\lockset; ensures \\lockset; \n" +
			"  void m6() { \n" +
			"  } \n" +
			" \n" +
			"  //@ also modifies \\lockset; ensures \\lockset == \\lockset; ensures \\lockset; \n" +
			"  void m6also() { \n" +
			"  } \n" +
			" \n" +
			"  //@ exsures (Throwable t) true; \n" +
			"  //@ also_exsures (SomeException se) se != null; \n" +
			"  //@ also_exsures (Throwable t) t == 5; \n" +
			"  //@ also_exsures (SomeSubException sse) false; \n" +
			"  //@ also_exsures (SomeOtherException soe) soe != null; \n" +
			"  //@ also_exsures (NullPointerException npe) true; \n" +
			"  //@ also_exsures (\\TYPE tt) tt == \\type(SomeException); \n" +
			"  //@ also_exsures (AnotherException ae) ae == null; \n" +
			"  void m10() throws SomeSubException, AnotherException { \n" +
			"  } \n" +
			" \n" +
			"  //@ also  \n" +
			"  //@ exsures (SomeException se) se != null; \n" +
			"  //@ exsures (Throwable t) t == 5; \n" +
			"  //@ exsures (SomeSubException sse) false; \n" +
			"  //@ exsures (SomeOtherException soe) soe != null; \n" +
			"  //@ exsures (NullPointerException npe) true; \n" +
			"  //@ exsures (\\TYPE tt) tt == \\type(SomeException); \n" +
			"  //@ exsures (AnotherException ae) ae == null; \n" +
			"  void m10also() throws SomeSubException, AnotherException { \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_162() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusSpec.java", 
			"class SomeException extends Throwable { \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_163() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusSpec.java", 
			"class SomeOtherException extends Throwable { \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_164() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusSpec.java", 
			"class SomeSubException extends SomeException { \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_165() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusSpec.java", 
			"class AnotherException extends RuntimeException { \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_166() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusSpec.java", 
			"class FClass { \n" +
			"  int y = 4; \n" +
			"  final int x = 5; \n" +
			"  static final boolean b = false; \n" +
			"  final int[] a; \n" +
			" \n" +
			"  //@ modifies x, this.x, this.b, FClass.b; \n" +
			"  //@ modifies b, y; \n" +
			"  //@ modifies a, a.length, a[4], a[*] \n" +
			"  void m() { \n" +
			"  } \n" +
			" \n" +
			"  //@ modifies b, f.x; \n" +
			"  static void p(FClass f) { \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_167() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusSpec.java", 
			"class FFClass extends FClass { \n" +
			"  final int xx = 5; \n" +
			"  static final boolean bb = false; \n" +
			"   \n" +
			"  //@ also_modifies this.xx; \n" +
			"  //@ also_modifies x, y, b; \n" +
			"  //@ also_modifies bb; \n" +
			"  void m() { \n" +
			"  } \n" +
			" \n" +
			"  //@ also modifies this.xx; \n" +
			"  //@ modifies x, y, b; \n" +
			"  //@ modifies bb; \n" +
			"  void malso() { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_168() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusFunctions.java", 
			"// These tests test the argument types and return types of special ESC/Java functions \n" +
			" \n" +
			"class BogusFunctions { \n" +
			"  //@ ghost public \\TYPE tt; \n" +
			"  //@ ghost public int ii; \n" +
			"  //@ ghost public int[][] ga; \n" +
			"  Cloneable[] aa; \n" +
			"   \n" +
			"  void mTypes() { \n" +
			"    //@ assert \\type(BogusFunctions) <: \\type(Object); \n" +
			"    //@ assert tt <: (\\TYPE)tt; \n" +
			"    //@ assert \\elemtype(tt) <: tt; \n" +
			"    //@ set tt = tt <: (\\TYPE)tt ? \\type(BogusFunctions[]) : \\typeof(this); \n" +
			"    //@ assert \\elemtype(\\typeof(this)) == \\elemtype(\\elemtype(\\elemtype(\\type(Object)))); \n" +
			" \n" +
			"    /*@ set ii = \\type(Cloneable); */  // illegal \n" +
			"    /*@ assert (\\type(Object) <: \\typeof(this)) == 12; */ // illegal \n" +
			"    /*@ assert \\type(java.lang.Object[]); */  // illegal \n" +
			"    /*@ assert \\elemtype(\\type(java.lang.Object[])); */  // illegal \n" +
			"    /*@ assert \\elemtype(5 < 5) == \\elemtype((\\TYPE)this); */  // illegal \n" +
			"  } \n" +
			" \n" +
			"  //@ ghost public \\TYPE[][] mENNghost0; \n" +
			"  //@ ghost public \\TYPE[] mENNghost1; \n" +
			"  void mElemsnonnull() { \n" +
			"    Object[] a = new Object[0]; \n" +
			"    //@ assert \\nonnullelements(a); \n" +
			"    //@ assert \\nonnullelements(ga); \n" +
			"    //@ assert \\nonnullelements(aa); \n" +
			"    //@ assert \\nonnullelements(mENNghost0); \n" +
			" \n" +
			"    int[] b = null; \n" +
			"    /*@ assert \\nonnullelements(b); */  // illegal \n" +
			"    /*@ assert \\nonnullelements(12); */  // illegal \n" +
			"    /*@ assert \\nonnullelements(12 < 13); */  // illegal \n" +
			"    /*@ assert \\nonnullelements(a) == 12; */  // illegal \n" +
			"    //@ assert \\nonnullelements(mENNghost1); \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\fresh(this); \n" +
			"  //@ ensures \\fresh(null); \n" +
			"  /*@ ensures \\fresh(tt); */  // illegal \n" +
			"  /*@ ensures \\fresh(ii); */  // illegal \n" +
			"  /*@ ensures \\fresh(); */  // illegal \n" +
			"  /*@ ensures \\fresh(this, null); */  // now ok \n" +
			"  void mFresh() { \n" +
			"  } \n" +
			" \n" +
			"  //@ modifies ii, tt \n" +
			"  //@ ensures \\old(ii) == ii; \n" +
			"  //@ ensures tt == \\old(tt); \n" +
			"  //@ ensures (\\forall BogusFunctions bf; bf.aa != null) ==> \\old((\\forall BogusFunctions bf; bf.aa != null)); \n" +
			"  /*@ ensures \\old(ii) == \\old(tt); */  // illegal \n" +
			"  /*@ ensures \\old() == \\old(ii, ii); */  // illegal \n" +
			"  void mPRE() { \n" +
			"  } \n" +
			" \n" +
			"  void mMutexOps() { \n" +
			"    int[] a = new int[1]; \n" +
			"    //@ assume \\lockset[this]; \n" +
			"    //@ assume \\max(\\lockset) <= \\max(\\lockset); \n" +
			"    //@ assume \\max(\\lockset) < \\max(\\lockset); \n" +
			"    //@ assume \\max(\\lockset) == \\max(\\lockset); \n" +
			"    //@ assume \\max(\\lockset) != \\max(\\lockset); \n" +
			"    //@ assume (\\max(\\lockset) < \\max(\\lockset)) == (3 < 4); \n" +
			" \n" +
			"    /*@ assume (\\max(\\lockset) < 4) == (3 < \\max(\\lockset)); */  // illegal \n" +
			"    /*@ assume \\max() == \\max(this); */  // illegal \n" +
			"    /*@ assume \\max(\\lockset) > \\max(\\lockset); */  // illegal \n" +
			"    /*@ assume \\max(\\lockset) >= \\max(\\lockset); */  // illegal \n" +
			"    /*@ assume \\lockset[12]; */  // illegal \n" +
			"    /*@ assume a[this] == 12; */  // illegal \n" +
			"    /*@ assume \\lockset[this] == 12; */  // illegal \n" +
			"    /*@ assume \\max(12, 13) == 13; */  // illegal \n" +
			"    /*@ assume (\\max(\\lockset) < \\max(\\lockset)) == 3; */  // illegal \n" +
			"  } \n" +
			" \n" +
			"  // All of the following are allowed: \n" +
			"  //@ requires null < this; \n" +
			"  //@ requires null < null; \n" +
			"  //@ requires this < null; \n" +
			"  //@ requires o < this && this < null && null < o; \n" +
			"  //@ requires this < o && null < this && o < null; \n" +
			"  //@ requires null <= this; \n" +
			"  //@ requires null <= null; \n" +
			"  //@ requires this <= null; \n" +
			"  //@ requires o <= this && this <= null && null <= o; \n" +
			"  //@ requires this <= o && null <= this && o <= null; \n" +
			"  //@ requires \\lockset[null]; \n" +
			"  void nullBelow(Object o) { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_169() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse6.java", 
			"class WontEvenParse6 { \n" +
			"  void m(int x) { \n" +
			"    MyLabel: \n" +
			"    //@ assert x == x; \n" +
			"    x++; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_170() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusVisibility.java", 
			"class BogusVisibility { \n" +
			"  private int priv; \n" +
			"  int pack; \n" +
			"  protected int prot; \n" +
			"  public int publ; \n" +
			"  /*@ spec_public */ private int spub0; \n" +
			"  /*@ spec_public */ int spub1; \n" +
			"  /*@ spec_public */ protected int spub2; \n" +
			"  /*@ spec_public */ public int spub3; \n" +
			"   \n" +
			"  private static int privSt; \n" +
			"  static int packSt; \n" +
			"  protected static int protSt; \n" +
			"  public static int publSt; \n" +
			"  /*@ spec_public */ private static int spub0St; \n" +
			"  /*@ spec_public */ static int spub1St; \n" +
			"  /*@ spec_public */ protected static int spub2St; \n" +
			"  /*@ spec_public */ public static int spub3St; \n" +
			"   \n" +
			"  private Object privMu; \n" +
			"  Object packMu; \n" +
			"  protected Object protMu; \n" +
			"  public Object publMu; \n" +
			"  /*@ spec_public */ private Object spub0Mu; \n" +
			"  /*@ spec_public */ Object spub1Mu; \n" +
			"  /*@ spec_public */ protected Object spub2Mu; \n" +
			"  /*@ spec_public */ public Object spub3Mu; \n" +
			"   \n" +
			"  // -----  readable_if \n" +
			"   \n" +
			"  /*@ readable_if priv == 0; */ private int defifPriv0; \n" +
			"  /*@ readable_if pack == 0; */ private int defifPriv1; \n" +
			"  /*@ readable_if prot == 0; */ private int defifPriv2; \n" +
			"  /*@ readable_if publ == 0; */ private int defifPriv3; \n" +
			"  /*@ readable_if spub0 == 0; */ private int defifPriv4; \n" +
			"  /*@ readable_if spub1 == 0; */ private int defifPriv5; \n" +
			"  /*@ readable_if spub2 == 0; */ private int defifPriv6; \n" +
			"  /*@ readable_if spub3 == 0; */ private int defifPriv7; \n" +
			"   \n" +
			"  /*@ readable_if priv == 0; */ int defifPack0; \n" +
			"  /*@ readable_if pack == 0; */ int defifPack1; \n" +
			"  /*@ readable_if prot == 0; */ int defifPack2; \n" +
			"  /*@ readable_if publ == 0; */ int defifPack3; \n" +
			"  /*@ readable_if spub0 == 0; */ int defifPack4; \n" +
			"  /*@ readable_if spub1 == 0; */ int defifPack5; \n" +
			"  /*@ readable_if spub2 == 0; */ int defifPack6; \n" +
			"  /*@ readable_if spub3 == 0; */ int defifPack7; \n" +
			"   \n" +
			"  /*@ readable_if priv == 0; */ protected int defifProt0; \n" +
			"  /*@ readable_if pack == 0; */ protected int defifProt1; \n" +
			"  /*@ readable_if prot == 0; */ protected int defifProt2; \n" +
			"  /*@ readable_if publ == 0; */ protected int defifProt3; \n" +
			"  /*@ readable_if spub0 == 0; */ protected int defifProt4; \n" +
			"  /*@ readable_if spub1 == 0; */ protected int defifProt5; \n" +
			"  /*@ readable_if spub2 == 0; */ protected int defifProt6; \n" +
			"  /*@ readable_if spub3 == 0; */ protected int defifProt7; \n" +
			"   \n" +
			"  /*@ readable_if priv == 0; */ public int defifPubl0; \n" +
			"  /*@ readable_if pack == 0; */ public int defifPubl1; \n" +
			"  /*@ readable_if prot == 0; */ public int defifPubl2; \n" +
			"  /*@ readable_if publ == 0; */ public int defifPubl3; \n" +
			"  /*@ readable_if spub0 == 0; */ public int defifPubl4; \n" +
			"  /*@ readable_if spub1 == 0; */ public int defifPubl5; \n" +
			"  /*@ readable_if spub2 == 0; */ public int defifPubl6; \n" +
			"  /*@ readable_if spub3 == 0; */ public int defifPubl7; \n" +
			" \n" +
			"  /*@ readable_if defifSelf == 0; */ protected int defifSelf; \n" +
			"   \n" +
			"  // -----  monitored_by \n" +
			" \n" +
			"  /*@ monitored_by privMu, packMu, protMu, publMu */ \n" +
			"  /*@ monitored_by spub0Mu, spub1Mu, spub2Mu, spub3Mu */ \n" +
			"  private int monbyPriv; \n" +
			"   \n" +
			"  /*@ monitored_by privMu, packMu, protMu, publMu */ \n" +
			"  /*@ monitored_by spub0Mu, spub1Mu, spub2Mu, spub3Mu */ \n" +
			"  int monbyPack; \n" +
			"   \n" +
			"  /*@ monitored_by privMu, packMu, protMu, publMu */ \n" +
			"  /*@ monitored_by spub0Mu, spub1Mu, spub2Mu, spub3Mu */ \n" +
			"  protected int monbyProt; \n" +
			"   \n" +
			"  /*@ monitored_by privMu, packMu, protMu, publMu */ \n" +
			"  /*@ monitored_by spub0Mu, spub1Mu, spub2Mu, spub3Mu */ \n" +
			"  public int monbyPubl; \n" +
			" \n" +
			"  /*@ monitored_by monbySelf */ \n" +
			"  protected Object monbySelf; \n" +
			"   \n" +
			"  // ----- requires \n" +
			" \n" +
			"  //@ requires priv == pack && prot == publ; \n" +
			"  //@ requires spub0 == spub1 && spub2 == spub3; \n" +
			"  private void reqPriv() {} \n" +
			" \n" +
			"  //@ requires priv == pack && prot == publ; \n" +
			"  //@ requires spub0 == spub1 && spub2 == spub3; \n" +
			"  void reqPack() {} \n" +
			" \n" +
			"  //@ requires priv == pack && prot == publ; \n" +
			"  //@ requires spub0 == spub1 && spub2 == spub3; \n" +
			"  protected void reqProt() {} \n" +
			" \n" +
			"  //@ requires priv == pack && prot == publ; \n" +
			"  //@ requires spub0 == spub1 && spub2 == spub3; \n" +
			"  public void reqPubl() {} \n" +
			" \n" +
			"  //@ requires reqProtSelf; \n" +
			"  protected void reqProtSelf() {} \n" +
			" \n" +
			"  // ----- ensures \n" +
			" \n" +
			"  //@ ensures priv == pack && prot == publ; \n" +
			"  //@ ensures spub0 == spub1 && spub2 == spub3; \n" +
			"  private void ens0() {} \n" +
			" \n" +
			"  //@ ensures priv == pack && prot == publ; \n" +
			"  //@ ensures spub0 == spub1 && spub2 == spub3; \n" +
			"  void ens1() {} \n" +
			" \n" +
			"  //@ ensures priv == pack && prot == publ; \n" +
			"  //@ ensures spub0 == spub1 && spub2 == spub3; \n" +
			"  protected void ens2() {} \n" +
			" \n" +
			"  //@ ensures priv == pack && prot == publ; \n" +
			"  //@ ensures spub0 == spub1 && spub2 == spub3; \n" +
			"  public void ens3() {} \n" +
			" \n" +
			"  //@ ensures priv == pack && prot == publ; \n" +
			"  //@ ensures spub0 == spub1 && spub2 == spub3; \n" +
			"  private final void ens4() {} \n" +
			" \n" +
			"  //@ ensures privSt == packSt && protSt == publSt; \n" +
			"  //@ ensures spub0St == spub1St && spub2St == spub3St; \n" +
			"  private static void ens5() {} \n" +
			" \n" +
			"  //@ ensures privSt == packSt && protSt == publSt; \n" +
			"  //@ ensures spub0St == spub1St && spub2St == spub3St; \n" +
			"  static void ens6() {} \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_171() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusVisibility.java", 
			"class BogusVisibilitySub extends BogusVisibility { \n" +
			"  private int privSub; \n" +
			"  private static int privSubSt; \n" +
			"  /*@ spec_public */ private int spub4; \n" +
			"  /*@ spec_public */ private static int spub4St; \n" +
			"   \n" +
			"  // ----- also_ensures \n" +
			" \n" +
			"  //@ also_ensures privSub == pack && prot == publ; \n" +
			"  //@ also_ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  //@ also_ensures spub0 == spub4; \n" +
			"  private void ens0() {} \n" +
			" \n" +
			"  //@ also ensures privSub == pack && prot == publ; \n" +
			"  //@ ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  //@ ensures spub0 == spub4; \n" +
			"  private void ens0also() {} \n" +
			" \n" +
			"  //@ also_ensures privSub == pack && prot == publ; \n" +
			"  //@ also_ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  void ens1() {} \n" +
			" \n" +
			"  //@ also ensures privSub == pack && prot == publ; \n" +
			"  //@ ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  void ens1also() {} \n" +
			" \n" +
			"  //@ also_ensures privSub == pack && prot == publ; \n" +
			"  //@ also_ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  protected void ens2() {} \n" +
			" \n" +
			"  //@ also ensures privSub == pack && prot == publ; \n" +
			"  //@ ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  protected void ens2also() {} \n" +
			" \n" +
			"  //@ also_ensures privSub == pack && prot == publ; \n" +
			"  //@ also_ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  public void ens3() {} \n" +
			" \n" +
			"  //@ also ensures privSub == pack && prot == publ; \n" +
			"  //@ ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  public void ens3also() {} \n" +
			" \n" +
			"  //@ also_ensures privSub == pack && prot == publ; \n" +
			"  //@ also_ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  private final void ens4() {} \n" +
			" \n" +
			"  //@ also ensures privSub == pack && prot == publ; \n" +
			"  //@ ensures spub4 == spub1 && spub2 == spub3; \n" +
			"  private final void ens4also() {} \n" +
			" \n" +
			"  //@ also_ensures privSubSt == packSt && protSt == publSt; \n" +
			"  //@ also_ensures spub4St == spub1St && spub2St == spub3St; \n" +
			"  private static void ens5() {} \n" +
			" \n" +
			"  //@ also ensures privSubSt == packSt && protSt == publSt; \n" +
			"  //@ ensures spub4St == spub1St && spub2St == spub3St; \n" +
			"  private static void ens5also() {} \n" +
			" \n" +
			"  //@ also_ensures privSubSt == packSt && protSt == publSt; \n" +
			"  //@ also_ensures spub4St == spub1St && spub2St == spub3St; \n" +
			"  static void ens6() {} \n" +
			" \n" +
			"  //@ also ensures privSubSt == packSt && protSt == publSt; \n" +
			"  //@ ensures spub4St == spub1St && spub2St == spub3St; \n" +
			"  static void ens6also() {} \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_172() {
			this.runNegativeTest(new String[] {
			testsPath + "BogusVisibility.java", 
			"class BogusVisibility2 { \n" +
			" \n" +
			"    void doit(BogusVisibility x) { \n" +
			"	int y = x.spub0;    // Error: spec_public only applies to annotations \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_173() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse2.java", 
			"class WontEvenParse2 { \n" +
			"  void m2() { \n" +
			"    //@ assert new Object(); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_174() {
			this.runNegativeTest(new String[] {
			testsPath + "SpecExprs1.java", 
			" \n" +
			"// Tests for resolution and typechecking of pragmas \n" +
			" \n" +
			"public abstract class SpecExprs1 { \n" +
			" \n" +
			"  public SpecExprs1[][] a1; \n" +
			" \n" +
			"  /*@ invariant typeof(a1) <: type(java.lang.Object[][]) */ \n" +
			"  /*@ invariant elemType(typeof(a1)) <: type(java.lang.Object[]) */ \n" +
			"  /*@ invariant elemType(typeof(a1)) == type(Modifiers1[]) */ \n" +
			"  /*@ invariant (forall int i,j; 0 <= i && i < a1.length  ) */ \n" +
			"  /*@ invariant (forall int i,j; (0 <= i && i < a1.length) \n" +
			"                               & (0 <= j && j < a1[i].length) ==> \n" +
			"                   a1[i][j] instanceof SpecExprs1) */ \n" +
			" \n" +
			"  public abstract void m1() \n" +
			"    /*@ modifies this.a1[*] */ \n" +
			"    ; \n" +
			" \n" +
			"  public abstract void m2(Object a1) \n" +
			"    /*@ ensures fresh(a1) & fresh(this.a1) */ \n" +
			"    /*@ ensures PRE(this.a1).length == this.a1.length */ \n" +
			"    /*@ ensures (forall int i; (i <= 0 & i < this.a1.length) \n" +
			"                  ==> this.a1[i] == PRE(this.a1)[i]) */ \n" +
			"    ; \n" +
			" \n" +
			"  public abstract void m3() \n" +
			"    /*@ requires LS[this.a1] */ \n" +
			"    ; \n" +
			" \n" +
			"  public abstract void m4(Object o) \n" +
			"    /*@ requires o < min(LS) */ \n" +
			"    ; \n" +
			" \n" +
			"  public abstract int[] permute(int[] a1, int[] a2) \n" +
			"    /*@ requires (forall int i,j;  \n" +
			"                   (0 <= i && i < a1.length) & (0 <= j && j < a2.length) \n" +
			"                   & a1[i] == a2[j] ==> i == j); */ \n" +
			"    /*@ ensures fresh(RES) */ \n" +
			"    /*@ ensures RES.length == (LBLPOS label1 a1.length) */ \n" +
			"    /*@ ensures (forall int i; (LBLNEG label2 (0 <= i && i < a1.length)) ==> \n" +
			"                  (exists int j; (0 <= j && j < a2.length)  \n" +
			"		                     ==> a1[i] == a2[j])); */ \n" +
			"    ; \n" +
			" \n" +
			"  public abstract void m5(SpecExprs1 other, int j) \n" +
			"    /*@ modifies other.a1, a1[j] */ \n" +
			"    ; \n" +
			" \n" +
			"  public abstract void m6(SpecExprs1 other, int j) \n" +
			"    /*@ requires (0 <= j && j < a1.length) */ \n" +
			"    /*@ modifies other.a1[*][*], this.a1[j][*] */ \n" +
			"    ; \n" +
			" \n" +
			"  public abstract void m7(SpecExprs1 other, int j) \n" +
			"    /*@ requires (forall int i; (0 <= i && i < a1.length)  \n" +
			"                                 ==> (0 <= j && j < a1[i].length)) */ \n" +
			"    /*@ modifies other.a1[*], a1[*][j] */ \n" +
			"    ; \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_175() {
			this.runNegativeTest(new String[] {
			testsPath + "Modifiers2.java", 
			" \n" +
			"// Tests for resolution and typechecking of pragmas \n" +
			" \n" +
			"public class Modifiers2 extends Modifiers1 { \n" +
			"  int v3; \n" +
			" \n" +
			"  public int update(Modifiers1 v1) \n" +
			"    /*@ also modifies v3; ensures v3 == this.v1 */ \n" +
			"  { \n" +
			"    v3 = this.v1; \n" +
			"    return super.update(v1); \n" +
			"  } \n" +
			"     \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_176() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeDeclElemPragmas1.java", 
			" \n" +
			"// Tests for resolution and typechecking of pragmas \n" +
			" \n" +
			"public abstract class TypeDeclElemPragmas1 extends Modifiers1 { \n" +
			" \n" +
			"  /*@ still_deferred v2; */ \n" +
			" \n" +
			"  /*@ axiom 0 < 1 */ \n" +
			" \n" +
			"  /*@ invariant 10 < v2 */ \n" +
			" \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_177() {
			this.runNegativeTest(new String[] {
			testsPath + "Modifiers1.java", 
			" \n" +
			"// Tests for resolution and typechecking of pragmas \n" +
			" \n" +
			"public class Modifiers1 { \n" +
			" \n" +
			"  /*@ monitored */ \n" +
			"  public Object mu1, mu2; \n" +
			" \n" +
			"  /*@ axiom mu1 < mu2 */ // Must hold mu1 before aquiring mu2 \n" +
			" \n" +
			"  /*@ writable_deferred */ \n" +
			"  public int v1 /*@ monitored_by mu1 */; \n" +
			" \n" +
			"  public int v2 /*@ monitored_by mu1, mu2; readable_if 10 < v1 */; \n" +
			" \n" +
			"  public int update(Modifiers1 v1) \n" +
			"    /*@ requires max(LS) == mu1 & 10 < v1.v1 */ \n" +
			"    /*@ modifies this.v1, v2 */ \n" +
			"    /*@ ensures (RES == PRE(this.v1)) & (this.v1 == v1.v1) */ { \n" +
			"      int result = this.v1; \n" +
			"      this.v1 = v1.v1; \n" +
			"      synchronized (mu2) { v2 = 10; } \n" +
			"      return result; \n" +
			"  } \n" +
			" \n" +
			"  public int find(int[] a, int el) \n" +
			"    /*@ requires (exists int i; 0 <= i & i < a.length & a[i] == el) */ \n" +
			"    /*@ ensures 0 <= RES & RES < a.length & a[RES] == el */ { \n" +
			"      int result = 0 /*@ uninitialized */; \n" +
			"      for(int i = 0; i < a.length; i++) \n" +
			"	if (a[i] == el) result = i; \n" +
			"      return result; \n" +
			"  } \n" +
			" \n" +
			" \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_178() {
			this.runNegativeTest(new String[] {
			testsPath + "C3.java", 
			"class C0 { \n" +
			"  int[] a; \n" +
			"  int n; \n" +
			" \n" +
			"  C0(int[] input) { \n" +
			"    n = input.length;  // null dereference \n" +
			"    a = new int[n]; \n" +
			"    System.arraycopy(input, 0, a, 0, n); \n" +
			"  } \n" +
			" \n" +
			"  // ... \n" +
			"   \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_179() {
			this.runNegativeTest(new String[] {
			testsPath + "C3.java", 
			"class C1 { \n" +
			"  int[] a; \n" +
			"  int n; \n" +
			" \n" +
			"  //@ requires input != null; \n" +
			"  C1(int[] input) { \n" +
			"    n = input.length; \n" +
			"    a = new int[n]; \n" +
			"    System.arraycopy(input, 0, a, 0, n); \n" +
			"  } \n" +
			" \n" +
			"  int extractMin() { \n" +
			"    int m = Integer.MAX_VALUE; \n" +
			"    int mi = 0; \n" +
			"    for (int i = 0; i < n; i++) { \n" +
			"      if (a[i] < m) {  // null dereference \n" +
			"	mi = i; \n" +
			"	m = a[i]; \n" +
			"      } \n" +
			"    } \n" +
			"    if (n != 0) { \n" +
			"      // Not yet implemented in checker:  n--; \n" +
			"      n = n - 1; \n" +
			"      a[mi] = a[n]; \n" +
			"    } \n" +
			"    return m; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_180() {
			this.runNegativeTest(new String[] {
			testsPath + "C3.java", 
			"class C2 { \n" +
			"  int[] a; \n" +
			"  //@ invariant a != null; \n" +
			"  int n; \n" +
			" \n" +
			"  //@ requires input != null; \n" +
			"  C2(int[] input) { \n" +
			"    n = input.length; \n" +
			"    a = new int[n]; \n" +
			"    System.arraycopy(input, 0, a, 0, n); \n" +
			"  } \n" +
			" \n" +
			"  int extractMin() { \n" +
			"    int m = Integer.MAX_VALUE; \n" +
			"    int mi = 0; \n" +
			"    for (int i = 0; i < n; i++) { \n" +
			"      if (a[i] < m) {  // array bounds error \n" +
			"	mi = i; \n" +
			"	m = a[i]; \n" +
			"      } \n" +
			"    } \n" +
			"    if (n != 0) { \n" +
			"      // Not yet implemented in checker:  n--; \n" +
			"      n = n - 1; \n" +
			"      a[mi] = a[n]; \n" +
			"    } \n" +
			"    return m; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_181() {
			this.runNegativeTest(new String[] {
			testsPath + "C3.java", 
			"public class C3 { \n" +
			"  int[] a; \n" +
			"  //@ invariant a != null; \n" +
			"  int n; \n" +
			"  //@ invariant 0 <= n && n <= a.length; \n" +
			" \n" +
			"  //@ requires input != null; \n" +
			"  C3(int[] input) { \n" +
			"    n = input.length; \n" +
			"    a = new int[n]; \n" +
			"    System.arraycopy(input, 0, a, 0, n); \n" +
			"  } \n" +
			" \n" +
			"  int extractMin() { \n" +
			"    int m = Integer.MAX_VALUE; \n" +
			"    int mi = 0; \n" +
			"    for (int i = 0; i < n; i++) { \n" +
			"      if (a[i] < m) { \n" +
			"	mi = i; \n" +
			"	m = a[i]; \n" +
			"      } \n" +
			"    } \n" +
			"    if (n != 0) { \n" +
			"      // Not yet implemented in checker:  n--; \n" +
			"      n = n - 1; \n" +
			"      a[mi] = a[n]; \n" +
			"    } \n" +
			"    return m; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_182() {
			this.runNegativeTest(new String[] {
			testsPath + "WontTypecheck.java", 
			"class WontTypecheck { \n" +
			"  //@ requires x < (* this should be an integer but isn't *); \n" +
			"  //@ requires (* this is fine *) ? (* but this is a boolean *) : x; \n" +
			"  //@ requires (* similarly *) ? x : (* now the boolean is here *); \n" +
			"  void m(int x) { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_183() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse1.java", 
			"class WontEvenParse1 { \n" +
			"  /*@ invariant (* this informal predicate has no end \n" +
			"   */ \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_184() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse3.java", 
			"class WontEvenParse3 { \n" +
			"  //@ axiom (*);   // not a proper informal predicate \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_185() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse0.java", 
			"class WontEvenParse0 { \n" +
			"  //@ invariant (* this informal predicate has no end \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_186() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			"  void a() { \n" +
			"    m(); \n" +
			"    p(); \n" +
			"    //@ assert ! (* this should generate a warning *); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (* this is an informal predicate *); \n" +
			"  //@ requires true &&(*soIsThis*) \n" +
			"  //@ ensures (((((* Here's one inside some parens *))))); \n" +
			"  void m() { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (* this has what looks like a // comment inside, but it isn't *) \n" +
			"  /*@ requires (* this one takes up more \n" +
			"                         than one line *); */ \n" +
			"  //@ requires (* one can even /* do this!! */;  cool, huh? *); \n" +
			"  //@ requires (* and /* this!! *); \n" +
			"  //@ ensures (**); \n" +
			"  /** This is a Javadoc comment <esc>ensures !!(*nothing fancy, really*)</esc> \n" +
			"   **/ \n" +
			"  void p() { \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires (\\forall int j; (* here's the range of j *); (* and \n" +
			"         here is the term *) && b[j] && (* and some more *)); */ \n" +
			"  void q(int x, /*@ non_null */ boolean[] b) { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_187() {
			this.runNegativeTest(new String[] {
			testsPath + "WontEvenParse2.java", 
			"class WontEvenParse2 { \n" +
			"  /** <esc> (* it is not possible to put \n" +
			"        this: </esc> inside an informal predicate *) </esc> \n" +
			"   **/ \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_188() {
			this.runNegativeTest(new String[] {
			testsPath + "Param.java", 
			"class Param { \n" +
			" \n" +
			"    void put(/*@ non_null @*/ String x) { \n" +
			"	if (\"hello\".equals(x)) \n" +
			"	    put(x); \n" +
			" \n" +
			"	x = null;			// error \n" +
			"    } \n" +
			" \n" +
			"    void doit(String y) { \n" +
			"	put(y);				// error \n" +
			"    } \n" +
			" \n" +
			"    void doit2(/*@ non_null @*/ String y) { \n" +
			"	put(y); \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_189() {
			this.runNegativeTest(new String[] {
			testsPath + "Inherit.java", 
			"class A { \n" +
			"    void put(/*@ non_null @*/ String x) { } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_190() {
			this.runNegativeTest(new String[] {
			testsPath + "Inherit.java", 
			"class B extends A { } \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_191() {
			this.runNegativeTest(new String[] {
			testsPath + "Inherit.java", 
			"class C extends B { \n" +
			" \n" +
			"    void put(String y) { \n" +
			"	//@ assert y != null \n" +
			" \n" +
			"	y = null;				// error \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_192() {
			this.runNegativeTest(new String[] {
			testsPath + "Methods.java", 
			"class Methods { \n" +
			"  /*@ non_null */ /*@ non_null */ /*@ non_null */ String m(String s) { \n" +
			"    return s; \n" +
			"  }  // warning: possibly null \n" +
			" \n" +
			"  //@ requires x == 0 ==> r != null; \n" +
			"  /*@ non_null */ Object p(int x, /*@ non_null */ String t, Object r) { \n" +
			"    switch (x) { \n" +
			"      case 0:  return r; \n" +
			"      default:  return t; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" +
			" \n" +
			"interface J { \n" +
			"  public /*@ non_null */ Object h(); \n" +
			"} \n" +
			" \n" +
			"interface K0 extends J { \n" +
			"} \n" +
			" \n" +
			"interface K1 extends J { \n" +
			"} \n" +
			" \n" +
			"interface L extends K0, K1 { \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_193() {
			this.runNegativeTest(new String[] {
			testsPath + "Methods.java", 
			"class M implements L { \n" +
			"  public Object h() { \n" +
			"    return null; \n" +
			"  }  // error:  null return \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_194() {
			this.runNegativeTest(new String[] {
			testsPath + "Methods.java", 
			"class N extends Methods { \n" +
			"  Object p(int x, String t, Object r) { \n" +
			"    return r; \n" +
			"  }  // possible error:  null return \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_195() {
			this.runNegativeTest(new String[] {
			testsPath + "Methods.java", 
			"class O extends N implements K1 { \n" +
			"  Object p(int x, String t, Object r) { \n" +
			"    return new Object(); \n" +
			"  } \n" +
			"  public Object h() { \n" +
			"    return p(5, \"hello\", null); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_196() {
			this.runNegativeTest(new String[] {
			testsPath + "Methods.java", 
			"class NowarnMe { \n" +
			"  /*@ non_null */ Object y0() { \n" +
			"    return null; \n" +
			"  }  //@ nowarn NonNullResult \n" +
			" \n" +
			"  /*@ non_null */  //@ nowarn NonNullResult \n" +
			"  Object y1() { \n" +
			"    return null; \n" +
			"  } \n" +
			" \n" +
			"  /*@ non_null */ Object y2() { \n" +
			"    return null; \n" +
			"  }  //@ nowarn \n" +
			" \n" +
			"  /*@ non_null */  //@ nowarn \n" +
			"  Object y3() { \n" +
			"    return null; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_197() {
			this.runNegativeTest(new String[] {
			testsPath + "Check.java", 
			"// This test file checks whether or not certain Null and NonNull checks are \n" +
			"// emitted. \n" +
			"// Note:  This test file is different from most, in that it is run with the -pgc \n" +
			"// switch.  The reason is that there is no easy to otherwise test whether a \n" +
			"// given check has been laid down. \n" +
			" \n" +
			"class CheckSuper { \n" +
			"  int f; \n" +
			"  /*@ non_null */ Check x; \n" +
			" \n" +
			"  /*@ non_null */ static Check g; \n" +
			"  static Check h; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_198() {
			this.runNegativeTest(new String[] {
			testsPath + "Check.java", 
			"class Check extends CheckSuper { \n" +
			"  /*@ non_null */ Check y; \n" +
			"  Check w; \n" +
			"  /*@ non_null */ static Check gg = new CheckSub(); \n" +
			" \n" +
			"  void m(/*@ non_null */ Check p, Check q) { \n" +
			"    int k = this.f; \n" +
			"    k = f; \n" +
			"    k = super.f; \n" +
			"    k = ((CheckSub)this).f;          // this performs a Cast check \n" +
			"    k = (this).f; \n" +
			" \n" +
			"    k = x.f; \n" +
			"    k = this.x.f; \n" +
			"    k = y.f; \n" +
			"    k = ((CheckSub)this).z.f;        // this performs a Cast check \n" +
			"     \n" +
			"    k = h.f;                         // this performs a Cast check \n" +
			"    k = g.f; \n" +
			"    k = CheckSuper.g.f; \n" +
			"    k = this.g.f; \n" +
			"    Check ee = null; \n" +
			"    k = ee.g.f; \n" +
			"    k = ((CheckSuper)null).g.f;      // this performs a Cast check \n" +
			"    k = gg.f; \n" +
			"     \n" +
			"    k = p.f; \n" +
			"    /*@ non_null */ Check r = p; \n" +
			"    k = r.f; \n" +
			" \n" +
			"    k = q.f;                         // this performs a Null check \n" +
			"    /*@ non_null */ Check s = q;     // this performs a NonNull check \n" +
			"    k = s.f; \n" +
			" \n" +
			"    Check t = p; \n" +
			"    k = t.f;                         // this performs a Null check \n" +
			"  } \n" +
			" \n" +
			"  Check(/*@ non_null */ Check p, Check q) { \n" +
			"    int k = x.f; \n" +
			"    k = y.f;                         // this performs a Null check \n" +
			"    k = ((CheckSub)this).z.f;        // this performs a Cast check \n" +
			" \n" +
			"    k = p.f; \n" +
			"    k = q.f;                         // this performs a Null check \n" +
			" \n" +
			"    k = h.f;                         // this performs a Cast check \n" +
			"    k = g.f; \n" +
			"    k = this.g.f; \n" +
			"    k = super.g.f; \n" +
			"    k = p.g.f; \n" +
			"    k = gg.f; \n" +
			"    k = this.gg.f; \n" +
			"    k = p.gg.f; \n" +
			" \n" +
			"    /*@ non_null */ Check r = p; \n" +
			"    k = r.f; \n" +
			"  } \n" +
			" \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_199() {
			this.runNegativeTest(new String[] {
			testsPath + "Check.java", 
			"class CheckSub extends Check { \n" +
			"  /*@ non_null */ Check z; \n" +
			" \n" +
			"  CheckSub() { \n" +
			"    super(null, null);               // this performs a NonNull check on the first parameter \n" +
			"    Check p = x; \n" +
			"    m(p, p);                         // this performs a NonNull check on the first parameter \n" +
			"    m(x, null); \n" +
			"    super.m(p, p);                   // this performs a NonNull check on the first parameter \n" +
			"    super.m(x, null); \n" +
			"    Check r = this; \n" +
			"    r.m(p, p);                       // this performs a Null check on \"r\" and a NonNull check on the first parameter \n" +
			"    r.m(x, null);                    // this performs a Null check on \"r\" \n" +
			"    /*@ non_null */ Check s = x; \n" +
			"    s.m(p, p);                       // this performs a NonNull check on the first parameter \n" +
			"    ((Check)(s)).m(x, null); \n" +
			"  } \n" +
			" \n" +
			"  void m(Check p, Check q) {  // this is a method override, so the parameters inherit any \"non_null\" modifier pragma \n" +
			"    int k = p.f; \n" +
			"    k = q.f;                         // this performs a Null check \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_200() {
			this.runNegativeTest(new String[] {
			testsPath + "Basic.java", 
			"class Basic { \n" +
			" \n" +
			"    /*@ non_null @*/ String x; \n" +
			" \n" +
			"    Basic() { }		// error: x not initialized to a non-null value \n" +
			" \n" +
			"    void doit() { \n" +
			"	//@ assert x != null	// no error \n" +
			" \n" +
			"	x = x;			// no error \n" +
			" \n" +
			"	x = null;		// error \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    //@ modifies x \n" +
			"    void changex() {} \n" +
			" \n" +
			"    void call() { \n" +
			"	changex(); \n" +
			" \n" +
			"	//@ assert x != null	// no error \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_201() {
			this.runNegativeTest(new String[] {
			testsPath + "Static.java", 
			"class Static { \n" +
			" \n" +
			"    static /*@ non_null @*/ String s = \"hello\"; \n" +
			" \n" +
			" \n" +
			"    void doit() { \n" +
			"	//@ assert s != null \n" +
			" \n" +
			"	s = null;			// error \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_202() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class TypeChecking { \n" +
			" \n" +
			"    /*@ non_null @*/ int x;	// error: non-reference type \n" +
			" \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_203() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class Top { \n" +
			"    void get(Object x) {} \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_204() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class Bottom extends Top { \n" +
			"    void get(/*@ non_null @*/ Object x) {}		// error: overrides! \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_205() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class Returns { \n" +
			" \n" +
			"  /*@ non_null @*/ Returns() { }  // error: cannot be used with constructor \n" +
			" \n" +
			"  /*@ non_null @*/ String name() { return \"hello\"; } \n" +
			" \n" +
			"  abstract /*@ non_null @*/ String m(); \n" +
			" \n" +
			"  /*@ non_null */ static Object p() { return new Object(); } \n" +
			" \n" +
			"  /*@ non_null */ int q0() { return 3; }  // error:  non-reference result type \n" +
			"  /*@ non_null */ void q1() { }  // error:  non-reference result type \n" +
			" \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_206() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class Ret { \n" +
			"  public /*@ non_null @*/ Object h() { return new Object(); } \n" +
			"} \n" +
			" \n" +
			"interface IReturn { \n" +
			"  public /*@ non_null @*/ Object h(); \n" +
			"} \n" +
			" \n" +
			"interface IReturn2 extends IReturn { \n" +
			"  public /*@ non_null @*/ Object h();  // error: cannot be used on override \n" +
			"} \n" +
			" \n" +
			"interface IReturn3 { \n" +
			"  public /*@ non_null @*/ Object h(); \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_207() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class EReturns0 extends Ret implements IReturn, IReturn3 { \n" +
			"  public /*@ non_null @*/ Object h() {  // error: cannot be used on override \n" +
			"    return new Object(); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_208() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class EReturns1 extends Ret { \n" +
			"  public /*@ non_null @*/ Object h() {  // error: cannot be used on override \n" +
			"    return new Object(); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_209() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class EReturns2 implements IReturn3 { \n" +
			"  public /*@ non_null @*/ Object h() {  // error: cannot be used on override \n" +
			"    return new Object(); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_210() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class EReturns3 extends Ret implements IReturn { \n" +
			"  public Object h() { \n" +
			"    return new Object(); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_211() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class EReturns4 extends EReturns3 implements IReturn3 { \n" +
			"  public Object h() { \n" +
			"    return new Object(); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_212() {
			this.runNegativeTest(new String[] {
			testsPath + "TypeChecking.java", 
			"class EReturns5 extends EReturns3 implements IReturn3, IReturn { \n" +
			"  public /*@ non_null */ Object h() {  // error: cannot be used on override \n" +
			"    return new Object(); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_213() {
			this.runNegativeTest(new String[] {
			testsPath + "Local.java", 
			"class Local { \n" +
			" \n" +
			"    //@ requires x != null \n" +
			"    void bar(String x) { \n" +
			"	/*@ non_null @*/ String s = x; \n" +
			" \n" +
			"	//@ assert s != null \n" +
			" \n" +
			"	s = null;			// error \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_214() {
			this.runNegativeTest(new String[] {
			testsPath + "NonNullInit.java", 
			"public class NonNullInit { \n" +
			"  /*@ non_null */ Object qq = new Object(); \n" +
			"  /*@ non_null */ Object nn; \n" +
			" \n" +
			"  NonNullInit(int x) { \n" +
			"    nn = this;  // this initializes \"nn\" \n" +
			"  } \n" +
			" \n" +
			"  NonNullInit(double x) { \n" +
			"    if (x < 0.0) { \n" +
			"      nn = new Object(); \n" +
			"    } \n" +
			"  }  // \"nn\" not initialized if \"if\" not taken \n" +
			" \n" +
			"  NonNullInit(Object x) { \n" +
			"    nn = x;  // this produces a NonNull error \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x != null; \n" +
			"  NonNullInit(Object x, Object y) { \n" +
			"    nn = x; \n" +
			"  } \n" +
			" \n" +
			"  NonNullInit(int[] a) { \n" +
			"    nn = qq; \n" +
			"  } \n" +
			" \n" +
			"  NonNullInit(int x, int y) { \n" +
			"  }  // fails to assign to \"nn\" \n" +
			" \n" +
			"  NonNullInit(double x, double y) { \n" +
			"    this((int)x, (int)y); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_215() {
			this.runNegativeTest(new String[] {
			testsPath + "D.java", 
			"class D { \n" +
			" \n" +
			"    static void n(Object[] a, Object[] b) \n" +
			"	//@ requires a.length > 0; \n" +
			"	//@ requires a != null; \n" +
			"	//@ requires b.length > 0; \n" +
			"	//@ requires b != null; \n" +
			"	//@ requires \\typeof(b) <: \\typeof(a); \n" +
			"	{ \n" +
			"	    // assert \\type(Object) <: \\elemtype(\\typeof(a)) \n" +
			"	    //@ assert a[0] == null | \\typeof(a[0]) <: \\type(Object); \n" +
			"	    //@ assert a[0] instanceof Object; \n" +
			"	    a[0] = b[0]; \n" +
			"	} \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_216() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			" \n" +
			"    static void n(Object[] a) \n" +
			"	//@ requires a.length > 0; \n" +
			"	//@ requires a != null; \n" +
			"	{ \n" +
			"	    // assert \\type(Object) <: \\elemtype(\\typeof(a)) \n" +
			"	    //@ assert a[0] == null | \\typeof(a[0]) <: \\type(Object); \n" +
			"	    //@ assert a[0] instanceof Object; \n" +
			"	} \n" +
			" \n" +
			"    static void m() { \n" +
			"	Object[] a = new Object[-1]; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_217() {
			this.runNegativeTest(new String[] {
			testsPath + "NullArr.java", 
			"/** \n" +
			" * $Id: NullArr.java 2198 2006-11-27 14:37:31Z chalin $ \n" +
			" * Test the new semantics of non_null as applied to array types. \n" +
			" * \n" +
			" * This test show the results of an intermediate implementation of the feature \n" +
			" * under which non_null applied to an array type constrains all array \n" +
			" * component types to be non_null. Once the feature is fully implemented, then \n" +
			" * it will be necessary to add non_null at the point indicated by !non_null. \n" +
			" */ \n" +
			"public class NullArr { \n" +
			" \n" +
			"    // Test argument types (all cases ok). \n" +
			"    public /*@non_null*/ Object m0a(/*@non_null*/ Object /*!non_null*/ [] a) { \n" +
			"	if(a.length > 1) \n" +
			"	    return a[0]; // Ok \n" +
			"	else \n" +
			"	    return \"\"; \n" +
			"    } \n" +
			" \n" +
			"    // Test argument types, error cases. \n" +
			"    public void m0b(/*@non_null*/ Object /*!non_null*/ [] a) { \n" +
			"	if(a.length > 1) \n" +
			"	    a[0] = null; // error \n" +
			"    } \n" +
			" \n" +
			"    // Test return type (all cases are ok). \n" +
			"    public /*@non_null*/ Object[] m1a(/*@non_null*/ Object /*!non_null*/ [] a) { \n" +
			"	switch (a.length) { \n" +
			"	case 1: \n" +
			"	    return a; \n" +
			"	case 2: \n" +
			"	    return new Object[0]; \n" +
			"	default: \n" +
			"	    Object [] result = { \"\" }; \n" +
			"	    return result; \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    // Test return type, error cases. \n" +
			"    public /*@non_null*/ Object[] m1b(/*@non_null*/ Object /*!non_null*/ [] a) { \n" +
			"	if(a.length == 331) { \n" +
			"	    return new Object[3]; // error \n" +
			"	} \n" +
			"	return a; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_218() {
			this.runNegativeTest(new String[] {
			testsPath + "NullArr1b.java", 
			"/** \n" +
			" * $Id: NullArr1b.java 2205 2006-11-27 20:41:48Z chalin $ \n" +
			" * Test cases for a fields of array types. \n" +
			" */ \n" +
			"public class NullArr1b { \n" +
			"    private /*@non_null*/ Object /*!non_null*/ [] a = new Object[0]; \n" +
			" \n" +
			"    public /*@non_null*/ Object m331() { \n" +
			"	if(a.length > 1) \n" +
			"	    return a[0]; // ok under new semantics. \n" +
			"	else \n" +
			"	    return \"\"; \n" +
			"    } \n" +
			" \n" +
			"    private /*@non_null*/ int[] ia331 = new int[1]; \n" +
			" \n" +
			"    public void mi331() { \n" +
			"        if(ia331.length > 1) \n" +
			"            ia331[0] = 1; // ok since ia is not a reference type. \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_219() {
			this.runNegativeTest(new String[] {
			testsPath + "ghost.java", 
			"class Ghost97 { \n" +
			"  //@ ghost public int[] i; \n" +
			"  //@ghost public boolean b; \n" +
			" \n" +
			" //@invariant b && (b == true) && (i[0] == 0); \n" +
			" \n" +
			"Ghost97() { \n" +
			"  int ok[]= {0,1}; \n" +
			"  int bad[]= {1,0}; \n" +
			"  //@set i= ok;  \n" +
			"  //@set b= true; \n" +
			"  if (this.m()) { \n" +
			"    //@set i= ok; \n" +
			"  } \n" +
			"  else { \n" +
			"    //@set i= bad; \n" +
			"} \n" +
			"} \n" +
			" \n" +
			"//@ requires true; \n" +
			"//@ ensures \\result == this.b \n" +
			"boolean m() \n" +
			"{ }  //@nowarn Post \n" +
			" \n" +
			" \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_220() {
			this.runNegativeTest(new String[] {
			testsPath + "Constr.java", 
			"public class Constr { \n" +
			"  int x; \n" +
			"  //@ invariant 5 <= x && x < 10; \n" +
			" \n" +
			"  // This constructor fails, since the zero-equivalent value for \"x\" \n" +
			"  // does not meet the invariant \n" +
			"  Constr() { \n" +
			"  } \n" +
			" \n" +
			"  // This constructor fails, because it doesn't list \"NullPointerException\" \n" +
			"  // in its throws set. \n" +
			"  Constr(double d) { \n" +
			"    throw new NullPointerException(); \n" +
			"  } \n" +
			" \n" +
			"  // This constructor should be just fine \n" +
			"  Constr(char ch) throws NullPointerException { \n" +
			"    throw new NullPointerException(); \n" +
			"  } \n" +
			" \n" +
			"  // This constructor should be just fine, too \n" +
			"  Constr(boolean b) throws NullPointerException, CException { \n" +
			"    throw new CException(); \n" +
			"  } \n" +
			" \n" +
			"  // This constructor is fine also \n" +
			"  Constr(double d0, double d1) throws Throwable { \n" +
			"    throw new CException(); \n" +
			"  } \n" +
			" \n" +
			"  // This constructor is not fine, because it destroys the \"Constr\" invariant \n" +
			"  // of its argument \n" +
			"  //@ requires c != null; \n" +
			"  Constr(Constr c) throws CException { \n" +
			"    c.x = 2; \n" +
			"    throw new CException(); \n" +
			"  } \n" +
			" \n" +
			"  // This constructor is not fine, since it may break the invariant of the \"Constr\" \n" +
			"  // object it allocates \n" +
			"  Constr(int y) throws CException { \n" +
			"    Constr c = new Constr(); \n" +
			"    c.x = y; \n" +
			"    throw new CException(); \n" +
			"  } \n" +
			"   \n" +
			"  // This constructor is fine, since the argument \"c\" couldn't possibly be \n" +
			"  // the object \"this\" being constructed \n" +
			"  Constr(Constr c, int y) { \n" +
			"    x = 8; \n" +
			"    if (c == this) { \n" +
			"      c.x = 2; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  // This constructor is fine, and declares that it never terminates normally \n" +
			"  //@ ensures false \n" +
			"  Constr(double d0, double d1, double d2) throws CException { \n" +
			"    throw new CException(); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_221() {
			this.runNegativeTest(new String[] {
			testsPath + "Constr.java", 
			"class ConstrSub extends Constr { \n" +
			"  int y; \n" +
			"  //@ invariant y < 0; \n" +
			" \n" +
			"  // This constructor should be fine \n" +
			"  ConstrSub() { \n" +
			"    y = -x; \n" +
			"  } \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_222() {
			this.runNegativeTest(new String[] {
			testsPath + "Constr.java", 
			"  // This constructor is fine.  If the superclass constructor terminates with an \n" +
			"  // exception, so will this constructor \n" +
			"  ConstrSub(int k, int m) throws Throwable { \n" +
			"    super(k == m); \n" +
			"    y -= 4;  //@ assert y == -4; \n" +
			"  } \n" +
			"   \n" +
			"  // This constructor is not fine, since it doesn't assign a negative value to \"y\" \n" +
			"  ConstrSub(char ch) { \n" +
			"  } \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_223() {
			this.runNegativeTest(new String[] {
			testsPath + "Constr.java", 
			"  // This constructor is fine, because the call to the superclass constructor never \n" +
			"  // terminates normally \n" +
			"  ConstrSub(double d) throws Throwable { \n" +
			"    super(d, d, d); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_224() {
			this.runNegativeTest(new String[] {
			testsPath + "Constr.java", 
			"class ConstrClient { \n" +
			"  // This method is fine \n" +
			"  void m0() { \n" +
			"    Constr c = new Constr(); \n" +
			"    //@ assert 5 <= c.x; \n" +
			"  } \n" +
			" \n" +
			"  // This method is fine \n" +
			"  void m1() { \n" +
			"    Constr c = null; \n" +
			"    boolean b = false; \n" +
			"    try { \n" +
			"      c = new ConstrSub(2.7); \n" +
			"    } catch (CException ce) { \n" +
			"      b = true; \n" +
			"    } catch (Throwable t) { \n" +
			"      b = true; \n" +
			"    } \n" +
			"    //@ assert !b ==> c != null && 5 <= c.x; \n" +
			"    //@ assert b ==> c == null; \n" +
			"  } \n" +
			" \n" +
			"  // This method is fine \n" +
			"  void m2() { \n" +
			"    try { \n" +
			"      Constr c = new Constr(2.7, 3.1, -1.0); \n" +
			"      //@ unreachable \n" +
			"    } catch (Throwable t) { \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  // This method is fine \n" +
			"  void m3() { \n" +
			"    Constr c = new Constr(); \n" +
			"    //@ assert 5 <= c.x; \n" +
			"    try { \n" +
			"      c = new Constr(c); \n" +
			"    } catch (CException ce) { \n" +
			"    } \n" +
			"    //@ assert 5 <= c.x; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_225() {
			this.runNegativeTest(new String[] {
			testsPath + "Constr.java", 
			"class CException extends Throwable { \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_226() {
			this.runNegativeTest(new String[] {
			testsPath + "loop.java", 
			" \n" +
			"public class loop { \n" +
			"  int m1_while_ok() { \n" +
			"    while (false) {} \n" +
			"  } \n" +
			"  int m2_while_fail() { \n" +
			"    while (false) {} \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"  int m3_while_ok() { \n" +
			"    while (true) {} \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"   \n" +
			"  int m1_do_ok() { \n" +
			"    do {} while (false); \n" +
			"  } \n" +
			"  int m2_do_fail() { \n" +
			"    do {} while (false); \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"  int m3_do_ok() { \n" +
			"    do {} while (true); \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"   \n" +
			"   \n" +
			"  int m1_for_ok() { \n" +
			"    for(;false;) {} \n" +
			"  } \n" +
			"  int m2_for_fail() { \n" +
			"    for(;false;) {} \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"  int m3_for_ok() { \n" +
			"    for(;true;) {} \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			" \n" +
			"  int r0_fast_finds_error() { \n" +
			"    int[] a = null; \n" +
			"    int i = 1; \n" +
			"    while (i <= 10) { \n" +
			"      a[i] = 0; // null dereference error \n" +
			"      i++; \n" +
			"    } \n" +
			"    return i; \n" +
			"  } \n" +
			" \n" +
			"  int r1_fast_misses_error() { \n" +
			"    int[] a = new int[10]; \n" +
			"    int i = 1; \n" +
			"    while (i <= 10) { \n" +
			"      a[i] = 0; // index out-of-bounds error \n" +
			"      i++; \n" +
			"    } \n" +
			"    return i; \n" +
			"  } \n" +
			" \n" +
			"  int r2_fast_finds_error(int[] a) \n" +
			"  /*@ requires a != null; */ \n" +
			"  { \n" +
			"    int i = 1; \n" +
			"    int s = 0; \n" +
			"    while (i <= a.length) { \n" +
			"      s += a[i]; // index out-of-bounds error \n" +
			"      i++; \n" +
			"    } \n" +
			"    return s; \n" +
			"  } \n" +
			"   \n" +
			"  int r3_fast_misses_error(int[] a) \n" +
			"  /*@ requires a != null; */ \n" +
			"  { \n" +
			"    //@ assume a.length == 10; \n" +
			"    int i = 1; \n" +
			"    int s = 0; \n" +
			"    while (i <= a.length) { \n" +
			"      s += a[i]; // index out-of-bounds error \n" +
			"      i++; \n" +
			"    } \n" +
			"    return s; \n" +
			"  } \n" +
			"   \n" +
			"  // The following test case was once used to home in on the error actually \n" +
			"  // detected by the next case. \n" +
			"  int r4_checker_is_off_the_hook(int[] a) \n" +
			"  /*@ requires a != null; */ \n" +
			"  { \n" +
			"    int i = 1; \n" +
			"    int s = 0; \n" +
			"    while (i <= a.length) { \n" +
			"      // the following assumption is bogus: \n" +
			"      //@ assume i < a.length; \n" +
			"      s += a[i]; // index out-of-bounds error \n" +
			"      i++; \n" +
			"    } \n" +
			"    return s; \n" +
			"  } \n" +
			" \n" +
			"  // The following test case once caused an error in the checker because \n" +
			"  // the \"length\" field, when occurring in a Java expression (as opposed \n" +
			"  // to in a SpecExpr), was not translated into an application of the \n" +
			"  // \"arrayLength\" function. \n" +
			"  int r5_no_error(int[] a) \n" +
			"  /*@ requires a != null; */ \n" +
			"  { \n" +
			"    int i = 1; \n" +
			"    int s = 0; \n" +
			"    while (i <= a.length) { \n" +
			"      if (i < a.length) \n" +
			"      { \n" +
			"        s += a[i]; \n" +
			"      } \n" +
			"      i++; \n" +
			"    } \n" +
			"    return s; \n" +
			"  } \n" +
			" \n" +
			"  // The following case contains no error.  It is intended to check whether \n" +
			"  // ESC/Java makes the \"break\" labels for the inner and outer loops distinct. \n" +
			"  void r6_no_error(int k) { \n" +
			"    int i = 0; \n" +
			"    Outer: \n" +
			"    while (i < 10) { \n" +
			"      int j = k; \n" +
			"      Inner: \n" +
			"      while (j < 10) { \n" +
			"        j++; \n" +
			"        if (j == 6) \n" +
			"        { \n" +
			"          break Outer; \n" +
			"	} \n" +
			"      } \n" +
			"      //@ assert j != 6; \n" +
			"      i++; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  // The following case contains no error.  It is intended to check whether \n" +
			"  // ESC/Java makes the \"break\" label for a loop distinct from \"ec$throw\". \n" +
			"  /*@ requires t != null; */ \n" +
			"  void r7_no_error(int j, Throwable t) { \n" +
			"    try { \n" +
			"      while (j < 10) { \n" +
			"        j++; \n" +
			"        if (j == 6) \n" +
			"        { \n" +
			"          throw t; \n" +
			"	} \n" +
			"      } \n" +
			"      //@ assert j != 6; \n" +
			"    } \n" +
			"    catch (Throwable tt) { \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  // The following case contains no error.  It is intended to check whether \n" +
			"  // ESC/Java makes the \"break\" label for a loop distinct from \"ec$return\". \n" +
			"  void r8_no_error(int j) { \n" +
			"    while (j < 10) { \n" +
			"      j++; \n" +
			"      if (j == 6) \n" +
			"      { \n" +
			"        return; \n" +
			"      } \n" +
			"    } \n" +
			"    //@ assert j != 6; \n" +
			"  } \n" +
			" \n" +
			"  void r9_fast_misses_error() { \n" +
			"    int j = 0; \n" +
			"    while (j < 10) { \n" +
			"      // loop_invariant j <= 10; \n" +
			"      j++; \n" +
			"    } \n" +
			"    // The error is that the following line really *is* reachable. \n" +
			"    //@ unreachable; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_227() {
			this.runNegativeTest(new String[] {
			testsPath + "loop.java", 
			"class loopinvariant extends loop { \n" +
			"  int j0_invariant() { \n" +
			"    int x = 0; \n" +
			"    /*@ loop_invariant x <= 10; */ \n" +
			"    while (x < 10) { \n" +
			"      x += 2; \n" +
			"    } \n" +
			"    return x; \n" +
			"  } \n" +
			" \n" +
			"  int j1_invariant() { \n" +
			"    int x = 0; \n" +
			"    /* loop_invariant \\old(x) <= x && x <= 10 */ \n" +
			"    while (x < 10) { \n" +
			"      x += 2; \n" +
			"    } \n" +
			"    // assert \\old(x) == 5; \n" +
			"    return x; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_228() {
			this.runNegativeTest(new String[] {
			testsPath + "loop.java", 
			" \n" +
			"public class loop { \n" +
			"  int m1_while_ok() { \n" +
			"    while (false) {} \n" +
			"  } \n" +
			"  int m2_while_fail() { \n" +
			"    while (false) {} \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"  int m3_while_ok() { \n" +
			"    while (true) {} \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"   \n" +
			"  int m1_do_ok() { \n" +
			"    do {} while(false); \n" +
			"  } \n" +
			"  int m2_do_fail() { \n" +
			"    do {} while(false); \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"  int m3_do_ok() { \n" +
			"    do {} while (true); \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"   \n" +
			"   \n" +
			"  int m1_for_ok() { \n" +
			"    for(;false;) {} \n" +
			"  } \n" +
			"  int m2_for_fail() { \n" +
			"    for(;false;) {} \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"  int m3_for_ok() { \n" +
			"    for(;true;) {} \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"   \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_229() {
			this.runNegativeTest(new String[] {
			testsPath + "LiteralTypes.java", 
			"class LiteralTypes { \n" +
			"  void m() { \n" +
			"    Object[] a = new Object[3]; \n" +
			"    a[0] = \"foo\"; \n" +
			"    a[1] = null; \n" +
			"    a[2] = LiteralTypes.class; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_230() {
			this.runNegativeTest(new String[] {
			testsPath + "Error3.java", 
			"class Error3 { \n" +
			"  // The following is not allowed, because additional @-signs \n" +
			"  // on the first line of a \"/*\"-comment cannot have any intervening \n" +
			"  // white space. \n" +
			" \n" +
			"  /*@ @@@@@@  requires x instanceof Error3 */ \n" +
			"  // ^ This is the problem. \n" +
			"  void r(Object x) { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_231() {
			this.runNegativeTest(new String[] {
			testsPath + "Error4.java", 
			"class Error4 { \n" +
			"  // The following is not allowed, because the @-signs must be contiguous. \n" +
			" \n" +
			"  /*@@@@@ \n" +
			"    @@@@@      requires \n" +
			"    @@ @@@@@@  x \n" +
			"    @@@        instanceof \n" +
			"    @          Error4;   @@@*/ \n" +
			"  void r(Object x) { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_232() {
			this.runNegativeTest(new String[] {
			testsPath + "Error1.java", 
			"class Error1 { \n" +
			"  // The following is not allowed, because additional @-signs \n" +
			"  // are ignored only in \"/*\"-comments. \n" +
			" \n" +
			"  //@@@@@@@@ requires x instanceof Error1 \n" +
			"  void r(/*@@@@@@@@ non_null @@@@@*/ Object x) { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_233() {
			this.runNegativeTest(new String[] {
			testsPath + "Error0.java", 
			"class Error0 { \n" +
			"  int[] a; \n" +
			" \n" +
			"  // The following pragma is not syntactically valid, because \n" +
			"  // inside JavaDoc comments, the non-white character that is \n" +
			"  // skipped at the beginning of a line is '*', not '@'. \n" +
			"   \n" +
			"  /**     <esc>modifies a;</esc> \n" +
			"<esc>   ensures \\result instanceof Object[] ==> \n" +
			"  @             \\nonnullelements((Object[])\\result);</esc> \n" +
			"    */ \n" +
			"  Object m() { \n" +
			"    return a; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_234() {
			this.runNegativeTest(new String[] {
			testsPath + "Error2.java", 
			"class Error2 { \n" +
			"  // The following is not allowed, because trailing @-signs \n" +
			"  // are ignored only in \"/*\"-comments. \n" +
			"  // Actually - per the JML design doc - it is allowed, and has been fixed. \n" +
			"  //@ requires x instanceof Error2    @@@@@ \n" +
			"  void r(/*@@@@@@@@ non_null @@@@@*/ Object x) { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_235() {
			this.runNegativeTest(new String[] {
			testsPath + "D.java", 
			"class D { \n" +
			"  static int x; \n" +
			" \n" +
			"   \n" +
			"  /** Both of the following sets of pragmas are supposed to \n" +
			"    * be recognized by ESC/Java: \n" +
			"    *     <esc>ensures \\result < 0;</esc> \n" +
			"    * and: \n" +
			"    *     <esc>modifies x; ensures x < 0;</esc> \n" +
			"    */ \n" +
			"  static int p(int s, int t) { \n" +
			"    x = s; \n" +
			"    return t; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_236() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			"  /** The following has been syntactically-legal ESC/Java pragmas \n" +
			"    * since version 1.2.2. \n" +
			"    **/ \n" +
			" \n" +
			"  /*@ non_null  */ Object a; \n" +
			"  //@ invariant a instanceof C  ; \n" +
			"  /*@(comment goes here) invariant a instanceof int[] ==> \n" +
			"                 ((int[])a).length == 5; */ \n" +
			" \n" +
			"  /*@@   requires p != null;  ensures \n" +
			"       \\result != null */ \n" +
			"  /**     <esc>modifies a;</esc> \n" +
			"<esc>   ensures \\result instanceof Object[] ==> \n" +
			"                \\nonnullelements((Object[])\\result);</esc> \n" +
			"    */ \n" +
			"  /*  <esc> gibberish!! </esc> ****/ \n" +
			"  Object m(Integer p) { \n" +
			"    return p; \n" +
			"  } \n" +
			" \n" +
			"  /** The following have become syntactically-legal ESC/Java pragmas \n" +
			"    * since the JML changes after version 1.2.3. \n" +
			"    **/ \n" +
			" \n" +
			"  /*@ non_null @*/ Object b; \n" +
			"  //@ invariant b instanceof C  ; \n" +
			"  /*@ invariant \n" +
			"    @   b instanceof int[] ==> \n" +
			"    @   ((int[])b).length == 5; \n" +
			"    @*/ \n" +
			"  /*@@ invariant \n" +
			"    @@   b instanceof double[] ==> \n" +
			"    @@   ((double[])b).length == 5; \n" +
			"    @@*/ \n" +
			"   \n" +
			"  /*@@   requires p != null;  ensures \n" +
			"     @  \\result == \\result; */ \n" +
			"  /**     <esc>modifies a;</esc> \n" +
			"<esc>   ensures \\result instanceof Object[] ==> \n" +
			"  *             \\nonnullelements((Object[])\\result);</esc> \n" +
			"    */ \n" +
			"  /*  <esc> gibberish!! </esc> ****/ \n" +
			"  Object n(Integer p) { \n" +
			"    return new Integer(p.intValue()); \n" +
			"  } \n" +
			" \n" +
			"  /*@ \n" +
			"    @  requires x != null; \n" +
			"    @*/ \n" +
			"  void p(Object x) { \n" +
			"    //@ assert x != null; \n" +
			"  } \n" +
			" \n" +
			"  /*@ \n" +
			"      requires x != null; \n" +
			"    @*/ \n" +
			"  void q(Object x) { \n" +
			"    //@ assert x != null; \n" +
			"  } \n" +
			" \n" +
			"  void r(/*@@@@@@@@ non_null @@@@@*/ Object x) { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_237() {
			this.runNegativeTest(new String[] {
			testsPath + "I.java", 
			"public class I { \n" +
			" \n" +
			"  //@ invariant this.i >= 0; \n" +
			"  public int i; \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i >= 0 && j >= 0 && k >= 0; \n" +
			"    @  ensures \\result == i+j+k; \n" +
			"    @*/ \n" +
			"  public /*@ pure */ int test0(int i, int j, int k) { \n" +
			"    return i+j+k; \n" +
			"  } \n" +
			" \n" +
			"  /*@ ensures this.i == \\old(this.test0(o1.i, o2.i, o3.i/o3.i)); \n" +
			"    @*/ \n" +
			"  public void test1(I o1, I o2, I o3) { \n" +
			"    this.i = this.test0(o1.i, o2.i, o3.i/o3.i); //null(o1),null(o2),null(o3),divZero warnings \n" +
			"  } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_238() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			" \n" +
			"    C() {} \n" +
			"     \n" +
			"    static int m() \n" +
			"	//@ ensures \\result == 0; \n" +
			"	{ \n" +
			"	    return n(); \n" +
			"	} \n" +
			" \n" +
			"    static int n() \n" +
			"	//@ ensures \\result == 0; \n" +
			"	{ \n" +
			"	    return 0; \n" +
			"	} \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_239() {
			this.runNegativeTest(new String[] {
			testsPath + "ooo.java", 
			"class ooo { \n" +
			"    void m(int a, int b) { \n" +
			"	/*@ assert a > 6 | b > 7; */ \n" +
			"        /*@ assert a > 6; */ \n" +
			" \n" +
			"    } \n" +
			" \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_240() {
			this.runNegativeTest(new String[] {
			testsPath + "Test306.java", 
			"public class Test306 {		 \n" +
			"	/*@non_null*/ final String s331 = \"a\";		 \n" +
			"	/*@nullable*/ String s555;		 \n" +
			"	//@ invariant s331.length() == s331.length();		 \n" +
			"	//@ invariant s555.length() == s555.length();		 \n" +
			"		 \n" +
			"	//@ requires s331.length() > 336;		 \n" +
			"	//@ requires s555.length() > 556;		 \n" +
			"	void m333() {		 \n" +
			"		int i = s331.hashCode();		 \n" +
			"	}		 \n" +
			"			 \n" +
			"	//@ requires i > 0;		 \n" +
			"	void m444(int i) {		 \n" +
			"	}		 \n" +
			"		 \n" +
			"	//@ invariant (\\forall int i; s331.length() == s331.length());		 \n" +
			"	//@ invariant (\\forall int i; s555.length() == s555.length());		 \n" +
			"}		 \n"		}, "ERROR");
			}

			public void test_241() {
			this.runNegativeTest(new String[] {
			testsPath + "T.java", 
			"/** \n" +
			" ** This file tests that FindContributors handles instance \n" +
			" ** initializer blocks correctly. \n" +
			" **/ \n" +
			" \n" +
			"class T { \n" +
			"    int k; \n" +
			"    //@ invariant k>0 \n" +
			" \n" +
			"    T() { \n" +
			"	k = 1; \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_242() {
			this.runNegativeTest(new String[] {
			testsPath + "T.java", 
			"class U extends T { \n" +
			"    { k = -1; } \n" +
			" \n" +
			"    U() {}       // Error \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_243() {
			this.runNegativeTest(new String[] {
			testsPath + "InstInit.java", 
			"class InstInit { \n" +
			"  int f = 2 + 3; \n" +
			"   \n" +
			"  { \n" +
			"    g = 6; \n" +
			"  } \n" +
			"   \n" +
			"  static { \n" +
			"    g++; \n" +
			"  } \n" +
			"   \n" +
			"  static int g = 5 + 7; \n" +
			" \n" +
			"  //@ requires 2 <= y; \n" +
			"  InstInit(int y) { \n" +
			"    x += y; \n" +
			"    //@ assert 50 <= x; \n" +
			"    //@ assert f == 11; \n" +
			"    //@ assert g == 13; \n" +
			"  } \n" +
			"   \n" +
			"  { \n" +
			"    f = f + g;  // 11 \n" +
			"    g = f + 2; // 13 \n" +
			"  } \n" +
			"   \n" +
			"  int x = 23; \n" +
			" \n" +
			"  { \n" +
			"    x++;  // 24 \n" +
			"    x += f;  // 35 \n" +
			"    x += g;  // 48 \n" +
			"  } \n" +
			"   \n" +
			"  InstInit() { \n" +
			"    x += 2; \n" +
			"    //@ assert x == 50; \n" +
			"    //@ assert f == 11; \n" +
			"    //@ assert g == 13; \n" +
			"  } \n" +
			" \n" +
			"  InstInit(int z0, int z1) { \n" +
			"    x += z0 + z1; \n" +
			"    //@ assert x == 50;   // fails \n" +
			"    //@ assert f == 11; \n" +
			"    //@ assert g == 13; \n" +
			"    //@ assert z0 == 2;   // fails \n" +
			"    /* from the assumptions about x, z0, and z1 above, z1 must be 0, so the next \n" +
			"       assertion will succeed */ \n" +
			"    //@ assert z1 == 0; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_244() {
			this.runNegativeTest(new String[] {
			testsPath + "Typecheck.java", 
			"class Typecheck { \n" +
			"  static void p() { } \n" +
			"  void m() { } \n" +
			"  static int x; \n" +
			"  int y; \n" +
			" \n" +
			"  //@ non_null \n" +
			"    { p(); } \n" +
			" \n" +
			"  //@ requires x < y; \n" +
			"  //@ ensures x + y + z;  // this doesn't even type check, but that's not checked \n" +
			"    { m(); } \n" +
			" \n" +
			"  //@ modifies x < y; \n" +
			"  //@ ensures x + y + z;  // this doesn't even type check, but that's not checked \n" +
			"  static { \n" +
			"    p(); \n" +
			"    m();  // can't do this in static initializer block \n" +
			"    y++;  // can't do this in static initializer block \n" +
			"    x++; \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures true; \n" +
			"  //@ nowarn Invariant; \n" +
			"  //@ monitored \n" +
			"    { y++; x++; m(); p(); } \n" +
			" \n" +
			"  //@ readable_if false; \n" +
			"  //@ monitored \n" +
			"  //@ monitored_by x << true; \n" +
			"  static { int z; z++; } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_245() {
			this.runNegativeTest(new String[] {
			testsPath + "N.java", 
			"class Super { \n" +
			"  public void m0(/*@ non_null */ int[] x) { \n" +
			"  } \n" +
			"  public void m1(int[] x, int[] y) { \n" +
			"  } \n" +
			"  public void m2(/*@ non_null */ int[] x) { \n" +
			"  } \n" +
			"  public void m3(/*@ non_null */ int[] x) { \n" +
			"  } \n" +
			"} \n" +
			" \n" +
			"interface J { \n" +
			"  public void m0(int[] x); \n" +
			"  public void m1(/*@ non_null */ int[] x, int[] y); \n" +
			"  public void m2(/*@ non_null */ int[] x); \n" +
			"  public void m4(/*@ non_null */ int[] x); \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_246() {
			this.runNegativeTest(new String[] {
			testsPath + "N.java", 
			"class N extends Super implements J { \n" +
			"  public void m0(int[] x) { \n" +
			"    //@ assert x != null; \n" +
			"  } \n" +
			"  public void m1(int[] x, int[] y) { \n" +
			"    //@ assert x != null; \n" +
			"    //@ assert y != null; \n" +
			"  } \n" +
			"  public void m2(int[] x) { \n" +
			"    //@ assert x != null; \n" +
			"  } \n" +
			"  public void m3(int[] x) { \n" +
			"    //@ assert x != null; \n" +
			"  } \n" +
			"  public void m4(int[] x) { \n" +
			"    //@ assert x != null; \n" +
			"  } \n" +
			" \n" +
			"  public void p(int which, int[] x) { \n" +
			"    switch (which){ \n" +
			"      case 0:  m0(x);  break; \n" +
			"      case 1:  m1(x, x);  break; \n" +
			"      case 2:  m2(x);  break; \n" +
			"      case 3:  m3(x);  break; \n" +
			"      case 4:  m4(x);  break; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_247() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class Super { \n" +
			"  //@ ensures 0 <= \\result; \n" +
			"  public int m(int x) { \n" +
			"    return 0; \n" +
			"  } \n" +
			"   \n" +
			"  //@ requires (x & 3) == 2; \n" +
			"  public int p(int x) { \n" +
			"    return 0; \n" +
			"  } \n" +
			"} \n" +
			" \n" +
			"interface J { \n" +
			"  //@ ensures \\result != x; \n" +
			"  public int m(int x); \n" +
			"   \n" +
			"  //@ requires x % 2 == 0; \n" +
			"  public int p(int x); \n" +
			"} \n" +
			" \n" +
			"interface K extends J { \n" +
			"  public int p(int x); \n" +
			"} \n" +
			" \n" +
			"interface M extends K, J { \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_248() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C extends Super implements J { \n" +
			"  //@ also ensures \\result < 10; \n" +
			"  public int m(int x) { \n" +
			"    return x+x; \n" +
			"  } \n" +
			"   \n" +
			"  public int p(int x) { \n" +
			"    //@ assert (x & 3) == 2; \n" +
			"    //@ assert x % 2 == 0; \n" +
			"    return 0; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_249() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class D implements M { \n" +
			"  //@ also requires x < 1000; \n" +
			"  public int p(int x) { \n" +
			"    //@ assert (x & 3) == 2; \n" +
			"    //@ assert x % 2 == 0; \n" +
			"    //@ assert x < 1000; \n" +
			"    return x; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_250() {
			this.runNegativeTest(new String[] {
			testsPath + "Typecheck.java", 
			"// This test concerns the use of preconditions and non_null parameter \n" +
			"// pragmas with instance methods. \n" +
			"// \n" +
			"// A method is \"class-new\" if it is declared in a class and does not \n" +
			"// override any method of any superclass.  A method is \"new\" if it doesn't \n" +
			"// override any method anywhere. \n" +
			"// \n" +
			"// Rules about non_null: \n" +
			"//   A non_null pragma may be place on an appropriately typed \n" +
			"//   parameters in \"new\" methods. \n" +
			"// \n" +
			"// Rules about requires: \n" +
			"//   A method can have a \"requires\" clause only if it is a new method. \n" +
			"// \n" +
			"// Rules about also_requires: \n" +
			"//   A method can have an \"also_requires\" clause only if it is a class-new \n" +
			"//   method that is not also a new method. \n" +
			" \n" +
			"class Super { \n" +
			"  public void m0(/*@ non_null */ int[] x) { \n" +
			"  } \n" +
			"  public void m1(int[] x) { \n" +
			"  } \n" +
			"  public void m2(int[] x) { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 0 <= k; \n" +
			"  public void p0(int k) { \n" +
			"  } \n" +
			"  //@ requires 0 <= k; \n" +
			"  public void p1(int k) { \n" +
			"  } \n" +
			"  /*@ also requires 0 <= k; */  // error: cannot put \"also requires\" here \n" +
			"  public void p2(int k) { \n" +
			"  } \n" +
			"} \n" +
			" \n" +
			"interface J { \n" +
			"  public void m0(int[] x); \n" +
			"  public void m1(int[] x); \n" +
			"  public void m2(/*@ non_null */ int[] x); \n" +
			"  public void m4(int[] x); \n" +
			"  public void m5(/*@ non_null */ int[] x); \n" +
			" \n" +
			"  //@ requires 0 <= k; \n" +
			"  public void p0(int k); \n" +
			"  //@ requires 0 <= k; \n" +
			"  public void p1(int k); \n" +
			"  /*@ also requires 0 <= k; */  // error: cannot put \"also requires\" here \n" +
			"  public void p2(int k); \n" +
			"  /*@ also requires 0 <= k; */  // error: cannot put \"alsorequires\" here \n" +
			"  public void p3(int k); \n" +
			"  public void p4(int k); \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_251() {
			this.runNegativeTest(new String[] {
			testsPath + "Typecheck.java", 
			"class Typecheck extends Super implements J { \n" +
			"  public void m0(/*@ non_null */ int[] x) { // error: method is not new \n" +
			"  } \n" +
			"  public void m1(/*@ non_null */ int[] x) { // error: method is not new \n" +
			"  } \n" +
			"  public void m2(/*@ non_null */ int[] x) { // error: method is not new \n" +
			"  } \n" +
			"  public void m3(/*@ non_null */ int[] x) { // fine:  method is new \n" +
			"  } \n" +
			"  public void m4(/*@ non_null */ int[] x) { // error:  method is class-new, not new \n" +
			"  } \n" +
			"  public void m5(/*@ non_null */ int[] x) { // error:  method is class-new, not new \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires 0 <= k; */   // error: cannot put \"requires\" here \n" +
			"  public void p0(int k) { \n" +
			"  } \n" +
			"  public void p1(int k) {  // fine \n" +
			"  } \n" +
			"  /*@ also requires 0 <= k; */  // error: cannot put \"also requires\" here \n" +
			"  public void p2(int k) { \n" +
			"  } \n" +
			"  /*@ also requires 0 <= k; */  // fine:  class-new methods are where \n" +
			"                                // \"also requires\" belong \n" +
			"  public void p3(int k) { \n" +
			"  } \n" +
			"  /*@ requires 0 <= k; */   // error: cannot put \"requires\" here (but \n" +
			"                            // \"also requires\" would work) \n" +
			"  public void p4(int k) { \n" +
			"  } \n" +
			"} \n" +
			" \n" +
			"interface K extends J { \n" +
			"  public void p(/*@ non_null */ int[] x);  // fine: method is new \n" +
			"  public void m0(/*@ non_null */ int[] x);  // error:  method is not new (or class-new) \n" +
			"  public void m2(/*@ non_null */ int[] x);  // error:  method is not new (or class-new) \n" +
			" \n" +
			"  /*@ requires 0 <= k; */   // error: cannot put \"requires\" here \n" +
			"  public void p0(int k); \n" +
			"  public void p1(int k);  // fine \n" +
			"  /*@ also requires 0 <= k; */  // error: cannot put \"also requires\" here \n" +
			"  public void p2(int k); \n" +
			"  /*@ also requires 0 <= k; */  // error: cannot put \"also requires\" here \n" +
			"  public void p3(int k); \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_252() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class T {} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_253() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C0 { \n" +
			"  T a = null; \n" +
			"  T b = new T(); \n" +
			"  T c; \n" +
			"  T d = ((T)((Object)null)); \n" +
			"  T e = a; \n" +
			"  /*@ non_null */ T k = null; \n" +
			" \n" +
			"  C0() { \n" +
			"  } \n" +
			" \n" +
			"  void m() { \n" +
			"    a = null; \n" +
			"    b = new T(); \n" +
			"    d = ((T)((Object)null)); \n" +
			"    e = a; \n" +
			"    k = null; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_254() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C1 { \n" +
			"  /*@ non_null */ T l = new T(); \n" +
			"  /*@ non_null */ T m; \n" +
			"  /*@ non_null */ T n = ((T)((Object)null)); \n" +
			" \n" +
			"  C1() { \n" +
			"  } \n" +
			" \n" +
			"  void m() { \n" +
			"    l = new T(); \n" +
			"    n = ((T)((Object)null)); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_255() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C2 { \n" +
			"  T b; \n" +
			"  /*@ non_null */ T o; \n" +
			" \n" +
			"  C2(int x) { \n" +
			"    switch (x) { \n" +
			"      case 0:  b = null; break; \n" +
			"      case 1:  o = null; break; \n" +
			"      case 2:  b = new T(); break; \n" +
			"      case 3:  o = new T(); break; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m(int x) { \n" +
			"    switch (x) { \n" +
			"      case 0:  b = null; break; \n" +
			"      case 1:  o = null; break; \n" +
			"      case 2:  b = new T(); break; \n" +
			"      case 3:  o = new T(); break; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_256() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C3 { \n" +
			"  T b; \n" +
			"  /*@ non_null */ T o; \n" +
			" \n" +
			"  { o = null; }  // always warns here \n" +
			" \n" +
			"  C3() { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_257() {
			this.runNegativeTest(new String[] {
			testsPath + "initstate.java", 
			"/** This test file contains a few tests that check that \n" +
			" ** the InitialState function equates variables with \n" +
			" ** their @pre versions. \n" +
			" **/ \n" +
			" \n" +
			"public class initstate { \n" +
			" \n" +
			"  static int g; \n" +
			" \n" +
			"  //@ requires 0 <= g; \n" +
			"  //@ ensures 0 <= \\result; \n" +
			"  int m0_ok() { \n" +
			"    return g; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires g < 10; \n" +
			"  //@ ensures \\result < 10; \n" +
			"  int m1_fail() { \n" +
			"    g= g + 1; \n" +
			"    return g; \n" +
			"  } \n" +
			" \n" +
			"  // This method fails for the following reason:  There is no modifies \n" +
			"  // clause, and in particular \"g\" does not appear in the modifies clause. \n" +
			"  // Therefore, \"\\old(g)\" in the postcondition is the same as just \"g\".  \n" +
			"  // However escjava will issue a caution. \n" +
			"  //@ requires g < 10; \n" +
			"  //@ ensures \\old(g) < 10; \n" +
			"  void m2_fail() { \n" +
			"    g= g + 1; \n" +
			"  } \n" +
			" \n" +
			"  // Here's the fix \n" +
			"  //@ requires g < 10; \n" +
			"  //@ modifies g; \n" +
			"  //@ ensures \\old(g) < 10; \n" +
			"  void m3_ok() { \n" +
			"    g= g + 1; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_258() {
			this.runNegativeTest(new String[] {
			testsPath + "mwhalen.java", 
			"// These test cases (or versions from which these were derived) provided \n" +
			"// by Mike Whalen.  (Many of these tests failed in previous ESC/Java versions.) \n" +
			" \n" +
			"class bing { } \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_259() {
			this.runNegativeTest(new String[] {
			testsPath + "mwhalen.java", 
			"class MyVector { \n" +
			"  void add(Object e) { \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_260() {
			this.runNegativeTest(new String[] {
			testsPath + "mwhalen.java", 
			"class mwhalen { \n" +
			"  //@ requires 0 <= n; \n" +
			"  void test0(int n) { \n" +
			"    int[] a = new int[n]; \n" +
			"     \n" +
			"    for (int i=0; i <= n; i++) { \n" +
			"      a[i] = 5; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void test1() {	 \n" +
			"    bing[] bingArray = new bing[1]; \n" +
			" \n" +
			"    for (int i=0; i <= 1; i++) { \n" +
			"      bingArray[i] = new bing(); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void test2() {	 \n" +
			"    bing[] bingArray = new bing[5]; \n" +
			" \n" +
			"    for (int i=0; i <= 5; i++) { \n" +
			"      bingArray[i] = new bing(); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void test3(bing oo) {	 \n" +
			"    bing[] bingArray = new bing[5]; \n" +
			" \n" +
			"    for (int i=0; i <= 5; i++) { \n" +
			"      bingArray[i] = oo; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void test4(bing oo) {	 \n" +
			"    bing[] bingArray = new bing[5]; \n" +
			" \n" +
			"    bingArray[0] = new bing(); \n" +
			"    bingArray[1] = new bing(); \n" +
			"    bingArray[2] = new bing(); \n" +
			"    bingArray[3] = new bing(); \n" +
			"    bingArray[4] = new bing(); \n" +
			"    bingArray[5] = new bing(); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 0 <= n; \n" +
			"  void test5(int n) {	 \n" +
			"    bing[] bingArray = new bing[n]; \n" +
			" \n" +
			"    for (int i=0; i <= n; i++) { \n" +
			"      bingArray[i] = new bing(); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void test6(int n, boolean b) {	 \n" +
			"    bing[] bingArray = new bing[5]; \n" +
			" \n" +
			"    for (int i=0; i <= 5; i++) { \n" +
			"      //@ assert n != i; \n" +
			"      bingArray[i] = new bing(); \n" +
			"    } \n" +
			"    //@ assert b; \n" +
			"  } \n" +
			" \n" +
			"  void test7(int n, boolean b) {	 \n" +
			"    bing[] bingArray = new bing[5]; \n" +
			" \n" +
			"    for (int i=0; i <= 5; i++) { \n" +
			"      //@ assert i < 2; \n" +
			"      bingArray[i] = new bing(); \n" +
			"    } \n" +
			"    //@ assert b; \n" +
			"  } \n" +
			" \n" +
			"  void test8(int n, boolean b) {	 \n" +
			"    bing[] bingArray = new bing[5]; \n" +
			" \n" +
			"    for (int i=0; i <= 5; i++) { \n" +
			"      //@ assert i < 1; \n" +
			"      bingArray[i] = new bing(); \n" +
			"    } \n" +
			"    //@ assert b; \n" +
			"  } \n" +
			" \n" +
			"  void test9(int n, boolean b) {	 \n" +
			"    bing[] bingArray = new bing[5]; \n" +
			" \n" +
			"    for (int i=0; i <= 5; i++) { \n" +
			"      //@ assert i < 2; \n" +
			"      P(); \n" +
			"      Object oo = bingArray[i]; \n" +
			"    } \n" +
			"    //@ assert b; \n" +
			"  } \n" +
			" \n" +
			"  int xx; \n" +
			"  //@ modifies xx; \n" +
			"  //@ ensures xx == \\old(xx)+1 \n" +
			"  void P() { xx++; } \n" +
			" \n" +
			"  void test10() { \n" +
			"    int[][] intArray = new int[5][]; \n" +
			" \n" +
			"    for (int i=0; i < 5; i++) { \n" +
			"      intArray[i] = new int[5]; \n" +
			"    } \n" +
			" \n" +
			"    //@ unreachable; \n" +
			"  } \n" +
			" \n" +
			"  void test11() { \n" +
			"    for (int i=0; i < 2; i++) { \n" +
			"      int[] a = new int[5]; \n" +
			"    } \n" +
			" \n" +
			"    //@ unreachable; \n" +
			"  } \n" +
			" \n" +
			"  void test12() { \n" +
			"    for (int i=0; i < 2; i++) { \n" +
			"      Object[] a = new Object[5]; \n" +
			"    } \n" +
			" \n" +
			"    //@ unreachable; \n" +
			"  } \n" +
			" \n" +
			"  void test13() { \n" +
			"    for (int i=0; i < 2; i++) { \n" +
			"      Object o = new Object(); \n" +
			"    } \n" +
			" \n" +
			"    //@ unreachable; \n" +
			"  } \n" +
			" \n" +
			"  void test14() { \n" +
			"    int x = 0; \n" +
			"    for (int i=0; i < 2; i++) { \n" +
			"      x++; \n" +
			"    } \n" +
			" \n" +
			"    //@ unreachable; \n" +
			"  } \n" +
			" \n" +
			"  void test15() { \n" +
			"    int[][] intArray = new int[5][]; \n" +
			" \n" +
			"    intArray[0] = new int[5]; \n" +
			"    intArray[1] = new int[5]; \n" +
			"    intArray[2] = new int[5]; \n" +
			"    intArray[3] = new int[5]; \n" +
			"    intArray[4] = new int[5]; \n" +
			" \n" +
			"    for (int i=0; i <= 5; i++) { \n" +
			"      for (int j=0; j <= 5; j++) { \n" +
			"	intArray[i][j] = -1; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			" \n" +
			"  //@ requires intArray != null; \n" +
			"  //@ requires intArray.length == 5; \n" +
			"  //@ requires intArray[0] != null; \n" +
			"  //@ requires intArray[0].length == 5; \n" +
			"  void test16(int[][] intArray) { \n" +
			"    for (int i=0; i <= 5; i++) { \n" +
			"      for (int j=0; j <= 5; j++) { \n" +
			"	intArray[i][j] = -1; \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void test17() { \n" +
			"    int x = 0; \n" +
			"    for (int i=0; i < 2; i++) { \n" +
			"      x++; \n" +
			"    } \n" +
			" \n" +
			"    //@ unreachable; \n" +
			"  } \n" +
			"   \n" +
			"  void test50() { \n" +
			"    MyVector v = new MyVector(); \n" +
			" \n" +
			"    for (int i=0; i < 5; i++) { \n" +
			"      v.add(new bing()); \n" +
			"    } \n" +
			" \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			" \n" +
			"  void test51() { \n" +
			"    MyVector v = new MyVector(); \n" +
			" \n" +
			"    v.add(new bing()); \n" +
			"    v.add(new bing()); \n" +
			"    v.add(new bing()); \n" +
			"    v.add(new bing()); \n" +
			"    v.add(new bing()); \n" +
			" \n" +
			"    //@ assert false; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_261() {
			this.runNegativeTest(new String[] {
			testsPath + "B.java", 
			"class B extends Object { \n" +
			"  //@ public model boolean isInit; \n" +
			" \n" +
			"  //@requires isInit; \n" +
			"  public abstract int m(); \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_262() {
			this.runNegativeTest(new String[] {
			testsPath + "D.java", 
			"class D extends B { \n" +
			"  private C a; \n" +
			"  //@ represents isInit = (a!=null && a.isInit); \n" +
			" \n" +
			"  public int m() { \n" +
			"    return a.m(); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_263() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C extends B { \n" +
			"  public int m() { \n" +
			"    return 1; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_264() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			" \n" +
			"  public static void main(String[] args) { \n" +
			" \n" +
			"    int[] a = { 1 }; \n" +
			"    sort2(a); \n" +
			"    // System.out.println(\"Min is \"+a[0]); \n" +
			"  } \n" +
			"   \n" +
			"  static void sort2(int[] a) \n" +
			"    { \n" +
			"      //@ assume a != null && a.length == 2; \n" +
			"       \n" +
			"      if( a[0] > a[1] ) { \n" +
			"	int t = a[0]; \n" +
			"	a[0] = a[2]; \n" +
			"	a[1] = t; \n" +
			"      } \n" +
			" \n" +
			"      //@ assert a[0] <= a[1]; \n" +
			"    } \n" +
			" \n" +
			"  static void sort2again(int[] a) \n" +
			"    { \n" +
			"      //@ assume a != null && a.length == 3; \n" +
			"       \n" +
			"      if( a[0] > a[1] ) { \n" +
			"	int t = a[0]; \n" +
			"	a[0] = a[2]; \n" +
			"	a[1] = t; \n" +
			"      } \n" +
			" \n" +
			"      //@ assert a[0] <= a[1];       // fails because a[2] should be a[1] \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_265() {
			this.runNegativeTest(new String[] {
			testsPath + "AllocMorass.java", 
			"class AllocMorass { \n" +
			"  AllocMorass f; \n" +
			"   \n" +
			"  void m0(AllocMorass am) { \n" +
			"    AllocMorass n = new AllocMorass(); \n" +
			"    //@ assert am.f != n; \n" +
			"  } \n" +
			" \n" +
			"  void m1() { \n" +
			"    AllocMorass n = new AllocMorass(); \n" +
			"    //@ assert this.f != n; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires am != null; \n" +
			"  //@ ensures this != am.f; \n" +
			"  AllocMorass(AllocMorass am) { \n" +
			"  } \n" +
			" \n" +
			"  AllocMorass() { \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_266() {
			this.runNegativeTest(new String[] {
			testsPath + "B.java", 
			"public class B { \n" +
			"	public Object m_result4() { // warning: nullable ignored \n" +
			"		return \"\"; \n" +
			"	} \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_267() {
			this.runNegativeTest(new String[] {
			testsPath + "A.java", 
			"public class A extends B { \n" +
			"	public A() { \n" +
			"	} \n" +
			" \n" +
			"	public Object m_result1() { \n" +
			"		return null; // warning: NonNullResult \n" +
			"	} \n" +
			" \n" +
			"	public Object m_result2(/*@nullable*/Object o) { \n" +
			"		return o; // warning: NonNullResult \n" +
			"	} \n" +
			" \n" +
			"	public Object m_result3() { \n" +
			"		return \"\"; \n" +
			"	} \n" +
			" \n" +
			"	// overrides \n" +
			"	public /*@nullable*/Object m_result4() { // warning: nullable ignored \n" +
			"		return \"\"; \n" +
			"	} \n" +
			" \n" +
			"	public /*@nullable*/Object m_result5() { \n" +
			"		return null; \n" +
			"	} \n" +
			" \n" +
			"	public int m_result_ok() { \n" +
			"		return 0; \n" +
			"	} \n" +
			" \n" +
			"	public Object m_param_result1(Object o) { \n" +
			"		return o; \n" +
			"	} \n" +
			" \n" +
			"	public void m_param1(int i) { \n" +
			"		i++; \n" +
			"	} \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_268() {
			this.runNegativeTest(new String[] {
			testsPath + "initializer.java", 
			" \n" +
			"class C { \n" +
			" \n" +
			"    C()  \n" +
			"    //@ ensures b == false \n" +
			"    { \n" +
			"	return; \n" +
			"    } \n" +
			" \n" +
			"    public boolean b = true || false; \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_269() {
			this.runNegativeTest(new String[] {
			testsPath + "return.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    static int m(boolean b) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	if (b) \n" +
			"	    return 1; \n" +
			"	else \n" +
			"	    return 0; \n" +
			"    } \n" +
			" \n" +
			"    static int n(boolean b) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	try { \n" +
			"	    if (b) \n" +
			"		return 0; \n" +
			"	    else \n" +
			"		return 1; \n" +
			"	} \n" +
			"	finally { \n" +
			"	    return 2; \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_270() {
			this.runNegativeTest(new String[] {
			testsPath + "condExpr.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    static int m(int i) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	int result; \n" +
			"	result = (i == 1 ? 1 : 0); \n" +
			"	return result; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_271() {
			this.runNegativeTest(new String[] {
			testsPath + "if.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    static int m(int i) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	if (i == 1) { \n" +
			"	    return 0; \n" +
			"	} \n" +
			"	else if (i == 2) { \n" +
			"	    return 0; \n" +
			"	} \n" +
			"	else { \n" +
			"	    return 2; \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_272() {
			this.runNegativeTest(new String[] {
			testsPath + "constructor.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() throws Exception  \n" +
			"    { \n" +
			"	throw new Exception(); \n" +
			"    } \n" +
			" \n" +
			"    int m(int i) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	try { \n" +
			"	    C c = new C(); \n" +
			"	    return 0; \n" +
			"	} \n" +
			"	catch (Exception e) { \n" +
			"	    return 1; \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_273() {
			this.runNegativeTest(new String[] {
			testsPath + "or.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    static int m(int i, int j) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	boolean b = (i == 1) || (j == 2); \n" +
			"	return i; \n" +
			"    } \n" +
			" \n" +
			"    static boolean m2(int i, int j) \n" +
			"    //@ requires i != 1 \n" +
			"    //@ ensures \\result == false \n" +
			"    { \n" +
			"	boolean b = (i == 1) || (j == 2); \n" +
			"	return b; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_274() {
			this.runNegativeTest(new String[] {
			testsPath + "break.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    static int m(int x) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	int res = 0; \n" +
			"	for(int i=0; i < x; i++) { \n" +
			"	    res = 1; \n" +
			"	    break; \n" +
			"	} \n" +
			"	return res; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_275() {
			this.runNegativeTest(new String[] {
			testsPath + "switch.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    static int m(int i) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	int x = 1; \n" +
			"	 \n" +
			"	switch (i) { \n" +
			"	case 1: \n" +
			"	    return 0; \n" +
			"	case 2: \n" +
			"	    x = 0; \n" +
			"	case 3: \n" +
			"	    return x; \n" +
			"	default: \n" +
			"	    return 0; \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    static int m2(int i) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	int x = 1; \n" +
			"	 \n" +
			"	switch (i) { \n" +
			"	case 1: \n" +
			"	    return 0; \n" +
			"	case 2: \n" +
			"	case 3: \n" +
			"	    x = 0; \n" +
			"	    return x; \n" +
			"	default: \n" +
			"	    break; \n" +
			"	} \n" +
			"	return 1; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_276() {
			this.runNegativeTest(new String[] {
			testsPath + "throw.java", 
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    static int m(boolean b) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	try { \n" +
			"	    if (b) \n" +
			"		return 0; \n" +
			"	    else \n" +
			"		throw new Throwable(); \n" +
			"	} \n" +
			"	catch (Throwable t) { \n" +
			"	    return 1; \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_277() {
			this.runNegativeTest(new String[] {
			testsPath + "verbose.java", 
			"class verbose { \n" +
			"  int x; \n" +
			"  //@ invariant x == 0; \n" +
			" \n" +
			"  void m(int y) { \n" +
			"    x = y; \n" +
			"    n(y); \n" +
			"  } \n" +
			" \n" +
			"  /*@ helper */ private void n(int y) { \n" +
			"  } \n" +
			" \n" +
			"  void p(int y) { \n" +
			"    m(y); \n" +
			"    x = y+1; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_278() {
			this.runNegativeTest(new String[] {
			testsPath + "continue.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    static int m(int x) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	for(int i=0; i < x; i++) { \n" +
			"	    continue; \n" +
			"	} \n" +
			"	return 1; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_279() {
			this.runNegativeTest(new String[] {
			testsPath + "and.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    static int m(int i, int j) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	boolean b = (j == 2) && (i == 1); \n" +
			"	return i; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_280() {
			this.runNegativeTest(new String[] {
			testsPath + "tryfinally.java", 
			"class tryfinally { \n" +
			"  //@ ensures \\result != 2; \n" +
			"  int m0() { \n" +
			"    int x = 0; \n" +
			"    try { \n" +
			"      x++; \n" +
			"    } finally { \n" +
			"      x++; \n" +
			"    } \n" +
			"    return x;  // trace label \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != 2; \n" +
			"  int m1() { \n" +
			"    int x = 0; \n" +
			"    try { \n" +
			"      x++; \n" +
			"    } finally { \n" +
			"      x++; \n" +
			"      return x;  // trace label \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != 2; \n" +
			"  int m2() { \n" +
			"    int x = 0; \n" +
			"    while (true) {  // trace label \n" +
			"      try { \n" +
			"	x++; \n" +
			"	break;  // trace label \n" +
			"      } finally {  // trace label \n" +
			"	x++; \n" +
			"      }  // trace label \n" +
			"    } \n" +
			"    return x;  // trace label \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != 2; \n" +
			"  int m3() { \n" +
			"    int x = 0; \n" +
			"    while (true) {  // trace label \n" +
			"      try { \n" +
			"	x++; \n" +
			"	break;  // trace label \n" +
			"      } finally {  // trace label \n" +
			"	x++; \n" +
			"	return x;  // trace label \n" +
			"      }  // no trace label \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != 2; \n" +
			"  int m4() { \n" +
			"    int x = 0; \n" +
			"    while (true) {  // trace label \n" +
			"      try { \n" +
			"	x++; \n" +
			"	return 2;  // trace label \n" +
			"      } finally {  // trace label \n" +
			"	x++; \n" +
			"      }  // trace label \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != 2; \n" +
			"  int m5() { \n" +
			"    int x = 0; \n" +
			"    while (true) {  // trace label \n" +
			"      try { \n" +
			"	x++; \n" +
			"      } finally { \n" +
			"	x++; \n" +
			"	throw new RuntimeException();  // trace label \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != 2; \n" +
			"  int m6() { \n" +
			"    int x = 0; \n" +
			"    while (true) {  // trace label \n" +
			"      try { \n" +
			"	x++; \n" +
			"	throw new RuntimeException();  // trace label \n" +
			"      } finally {  // trace label \n" +
			"	x++; \n" +
			"      }  // trace label \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != 2; \n" +
			"  int m7() { \n" +
			"    int x = 0; \n" +
			"    while (true) {  // trace label \n" +
			"      try { \n" +
			"	x++; \n" +
			"	throw new RuntimeException();  // trace label \n" +
			"      } finally {  // trace label \n" +
			"	x++; \n" +
			"	throw new RuntimeException();  // trace label \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != 2; \n" +
			"  int m8() { \n" +
			"    int x = 0; \n" +
			"    while (true) {  // trace label \n" +
			"      try { \n" +
			"	x++; \n" +
			"	continue;  // trace label \n" +
			"      } finally {  // trace label \n" +
			"	x++; \n" +
			"	throw new RuntimeException();  // trace label \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_281() {
			this.runNegativeTest(new String[] {
			testsPath + "methodCall.java", 
			" \n" +
			"class C { \n" +
			"     \n" +
			"    C() {} \n" +
			" \n" +
			"    int m(int i) \n" +
			"    //@ ensures \\result == 0 \n" +
			"    { \n" +
			"	try { \n" +
			"	    n(i); \n" +
			"	    return 0; \n" +
			"	} \n" +
			"	catch (Exception e) { \n" +
			"	    return 1; \n" +
			"	} \n" +
			"    } \n" +
			"     \n" +
			"    void n(int i) throws Exception \n" +
			"    { \n" +
			"	throw new Exception(); \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_282() {
			this.runNegativeTest(new String[] {
			testsPath + "ghost.java", 
			"class Ghost95 { \n" +
			"  //@ ghost public int[] a; \n" +
			"  //@ghost public boolean b; \n" +
			" \n" +
			"//@invariant b && (b == true)  \n" +
			"//@invariant  a.length == 2 \n" +
			"//@invariant (\\forall int i; 0 <= i && i < a.length ==> a[i] == 0); \n" +
			" \n" +
			" \n" +
			"Ghost95() { \n" +
			"   int[] ok= {0,0}; \n" +
			"  //@set a= ok;  \n" +
			"  //@set b= true; \n" +
			"} \n" +
			" \n" +
			"void m() { \n" +
			"//@ assert (a.length == 2) && b; \n" +
			" \n" +
			"} \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_283() {
			this.runNegativeTest(new String[] {
			testsPath + "Specials.java", 
			"/** \n" +
			" ** Make sure can't apply set to special fields like \"length\" \n" +
			" **/ \n" +
			" \n" +
			"class Specials { \n" +
			" \n" +
			"    int[] a; \n" +
			"    //@ ghost public int[] b \n" +
			" \n" +
			"    void foo() { \n" +
			"	//@ set a.length = 0 \n" +
			"	//@ set b.length = 0 \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_284() {
			this.runNegativeTest(new String[] {
			testsPath + "DoesntEvenParse2.java", 
			"class DoesntEvenParse2 { \n" +
			"  boolean[] b; \n" +
			"  //@ invariant (\\forall int j ; b[j] ;); \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_285() {
			this.runNegativeTest(new String[] {
			testsPath + "DoesntEvenParse0.java", 
			"class DoesntEvenParse0 { \n" +
			"  boolean[] b; \n" +
			"  //@ invariant (\\forall int j ; b[j] ; b[j] ; b[j]); \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_286() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			"  boolean[] b; \n" +
			"  int[] x; \n" +
			" \n" +
			"  //@ requires (\\forall int j; 0 <= j && j < b.length ==> b[j]); \n" +
			"  void m0() { \n" +
			"    m1(); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (\\forall int j;; 0 <= j && j < b.length ==> b[j]); \n" +
			"  void m1() { \n" +
			"    m2(); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (\\forall int j; 0 <= j && j < b.length; b[j]); \n" +
			"  void m2() { \n" +
			"    m0(); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (\\exists int j; 0 <= j && j < b.length && b[j]); \n" +
			"  void p0() { \n" +
			"    p1(); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (\\exists int j;; 0 <= j && j < b.length && b[j]); \n" +
			"  void p1() { \n" +
			"    p2(); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (\\exists int j; 0 <= j && j < b.length; b[j]); \n" +
			"  void p2() { \n" +
			"    p0(); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (\\forall int j; b[j] && x[j] > 0); \n" +
			"  void w0() { \n" +
			"    w1(); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (\\forall int j; b[j]; x[j] > 0); \n" +
			"  void w1() { \n" +
			"    w0();  // error \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (\\exists int j; b[j] ==> x[j] > 0); \n" +
			"  void w2() { \n" +
			"    w3();  // error \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (\\exists int j; b[j]; x[j] > 0); \n" +
			"  void w3() { \n" +
			"    w2(); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_287() {
			this.runNegativeTest(new String[] {
			testsPath + "DoesntEvenParse1.java", 
			"class DoesntEvenParse1 { \n" +
			"  boolean[] b; \n" +
			"  //@ invariant (\\forall int j ;; b[j] ; b[j]); \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_288() {
			this.runNegativeTest(new String[] {
			testsPath + "LoopX.java", 
			"class LoopX { \n" +
			" \n" +
			"  void m05(int[] a) { \n" +
			"    for (int i = 0; \n" +
			"	 i < a.length;  // fails only with loop >= 0.5 \n" +
			"	 i++) { \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m10(int x) { \n" +
			"    for (int i = 0; i < x; i++) { \n" +
			"      /*@ unreachable; */  // fails only with loop >= 1.0 \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m15(int x) { \n" +
			"    boolean b = true; \n" +
			"    for (int i = 0; i < x; i++) { \n" +
			"      if (i == 0) \n" +
			"	b = false; \n" +
			"    } \n" +
			"    /*@ assert b; */  // fails only with loop >= 1.5 \n" +
			"  } \n" +
			" \n" +
			"  void m20(int x) { \n" +
			"    for (int i = 0; i < x; i++) { \n" +
			"      /*@ assert i != 1; */  // fails only with loop >= 2.0 \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  void m25(int x) { \n" +
			"    int s = 0; \n" +
			"    int i = 0; \n" +
			"    while (i < x) { \n" +
			"      s += 10; \n" +
			"      i++; \n" +
			"    } \n" +
			"    /*@ assert s <= 10 */  // fails only with loop >= 2.5 \n" +
			"  } \n" +
			"   \n" +
			"  void m30(int x) { \n" +
			"    int s = 0; \n" +
			"    for (int i = 0; i < x; i++) { \n" +
			"      for (int j = 0; j < i; j++) { \n" +
			"	s += 2; \n" +
			"	/*@ assert s < 6; */  // fails only with loop >= 3.0 \n" +
			"      } \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m35(int x) { \n" +
			"    int s = 0; \n" +
			"    for (int i = 0; i < x; i++) { \n" +
			"      for (int j = 0; j < i; j++) { \n" +
			"	s += 2; \n" +
			"      } \n" +
			"    } \n" +
			"    /*@ assert s <= 5; */  // fails only with loop >= 3.5 \n" +
			"  } \n" +
			" \n" +
			"  void m40() { \n" +
			"    int i = 0; \n" +
			"    do { \n" +
			"      i++; \n" +
			"    } while (i < 4); \n" +
			"    /*@ assert i < 4; */  // fails only with loop >= 4.0 \n" +
			"  } \n" +
			"   \n" +
			"  //@ requires a != null && 4 <= a.length; \n" +
			"  void m45(int x, int[] a) { \n" +
			"    int i = 0; \n" +
			"    while (i < x) { \n" +
			"      i++; \n" +
			"    } \n" +
			"    int y = a[i];  // fails only with loop >= 4.5 \n" +
			"  } \n" +
			"   \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_289() {
			this.runNegativeTest(new String[] {
			testsPath + "uninitialized.java", 
			" \n" +
			"public class uninitialized { \n" +
			"  int m1(boolean b) { \n" +
			"    int t =0 /*@ uninitialized */; \n" +
			"    int f =0/*@ uninitialized */; \n" +
			"    if (b) t = 0; \n" +
			"    else f = 1; \n" +
			"    int result=0 /*@ uninitialized */; \n" +
			"    if (! b) result = f; \n" +
			"    else result = t; \n" +
			"    //@ assert b ==> result == 0; \n" +
			"    //@ assert !b ==> result == 1; \n" +
			"    return result; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_290() {
			this.runNegativeTest(new String[] {
			testsPath + "T.java", 
			"class T { \n" +
			"  T() { \n" +
			"    int x; \n" +
			"    x = m0();  //@ assert x == 0; \n" +
			"    x = m1();  //@ assert x == 1; \n" +
			"    x = m2();  //@ assert x == 2;  // warning \n" +
			"    x = m3();  //@ assert x == 3;  // warning \n" +
			"  } \n" +
			" \n" +
			"  T(int y) { \n" +
			"    int x; \n" +
			"    x = this.m0();  //@ assert x == 0; \n" +
			"    x = (this).m0();  //@ assert x == 0; \n" +
			"    x = ((T)this).m0();  //@ assert x == 0; \n" +
			"    T t = this; \n" +
			"    x = t.m0();  //@ assert x == 0;  // warning \n" +
			"  } \n" +
			" \n" +
			"  T(int z0, int z1) { \n" +
			"    this(z0+z1); \n" +
			"    int x = m0();  //@ assert x == 0;  // warning \n" +
			"  } \n" +
			" \n" +
			"  private int m0() { \n" +
			"    return 0; \n" +
			"  } \n" +
			" \n" +
			"  final int m1() { \n" +
			"    return 1; \n" +
			"  } \n" +
			" \n" +
			"  static int m2() { \n" +
			"    return 2; \n" +
			"  } \n" +
			" \n" +
			"  int m3() { \n" +
			"    return 3; \n" +
			"  } \n" +
			" \n" +
			"  int m4() { \n" +
			"    return 4; \n" +
			"  } \n" +
			" \n" +
			"  int m5() { \n" +
			"    return 5; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_291() {
			this.runNegativeTest(new String[] {
			testsPath + "T.java", 
			"class R extends T { \n" +
			"  R() { \n" +
			"    int x; \n" +
			"    x = m3(); //@ assert 0 <= x;  // warning \n" +
			"    x = m4(); //@ assert x == 14; \n" +
			"    x = m5(); //@ assert x == 5;  // warning \n" +
			"    x = super.m4();  //@ assert 0 <= x;  // warning \n" +
			"    x = super.m5();  //@ assert x == 5;  // warning \n" +
			"  } \n" +
			" \n" +
			"  int m3() { \n" +
			"    return 13; \n" +
			"  } \n" +
			" \n" +
			"  final int m4() { \n" +
			"    return 14; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_292() {
			this.runNegativeTest(new String[] {
			testsPath + "T.java", 
			"final class S extends T { \n" +
			"  S() { \n" +
			"    int x; \n" +
			"    x = m3();  //@ assert x == 3;  // warning \n" +
			"    x = m4();  //@ assert x == 24; \n" +
			"    x = m5();  //@ assert x == 25; \n" +
			"  } \n" +
			" \n" +
			"  final int m4() { \n" +
			"    return 24; \n" +
			"  } \n" +
			" \n" +
			"  int m5() { \n" +
			"    return 25; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_293() {
			this.runNegativeTest(new String[] {
			testsPath + "U.java", 
			"class U { \n" +
			"  int x; \n" +
			"  //@ invariant 10 <= x; \n" +
			"  int y; \n" +
			"  //@ invariant 10 <= y; \n" +
			"  int z; \n" +
			"  //@ invariant 10 <= z; \n" +
			" \n" +
			"  U(int tx, int ty, int tz) { \n" +
			"    x = 10; y = 10; z = 10;  // remove nondeterminism in which invariant is \n" +
			"                             // complained about below \n" +
			"    x = tx; \n" +
			"    m();  // invariant warning about x when checked without inlining \n" +
			"    y = ty; \n" +
			"    n();  // invariant warning about y when checked without inlining \n" +
			"    z = tz; \n" +
			"    o();  // invariant warning about z when checked without inlining \n" +
			"  } \n" +
			" \n" +
			"  final void m() { \n" +
			"    x = p(); \n" +
			"  }  // warning about x's invariant when checking m \n" +
			" \n" +
			"  private int p() { \n" +
			"    return 12; \n" +
			"  } \n" +
			" \n" +
			"  final void n() { \n" +
			"    y = q(); \n" +
			"  } \n" +
			" \n" +
			"  //@ helper \n" +
			"  private int q() { \n" +
			"    return 14; \n" +
			"  } \n" +
			" \n" +
			"  final void o() { \n" +
			"    z = r(18); \n" +
			"  }  // warning about z's invariant when checking o \n" +
			" \n" +
			"  //@ helper \n" +
			"  private int r(int t) { \n" +
			"    return s(t); \n" +
			"  } \n" +
			" \n" +
			"  private int s(int t) { \n" +
			"    return t; \n" +
			"  } \n" +
			" \n" +
			"  U(double tx) { \n" +
			"    x = 10; y = 10;   // remove nondeterminism in which invariant is \n" +
			"                      // complained about below \n" +
			"    rec(tx);  // invariant warning about z when checked without inlining \n" +
			"  } \n" +
			" \n" +
			"  private void rec(double dx) { \n" +
			"    if (dx < 0.0) { \n" +
			"      x = 10; y = 10; z = 10; \n" +
			"    } else { \n" +
			"      rec(dx - 1.0); \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_294() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			" \n" +
			"public class C { \n" +
			"    public static void test1() { \n" +
			"	int x; \n" +
			"	if( false ) { \n" +
			"	    x = 1; \n" +
			"	} else { \n" +
			"	    x = 2; \n" +
			"	} \n" +
			" \n" +
			"	//@ assert x==2; \n" +
			"    } \n" +
			" \n" +
			"    public static void test2() { \n" +
			"	int x=0; \n" +
			"	x=x+1; \n" +
			"	if( true ) x=x+2; \n" +
			"	if( false ) x=x+4; \n" +
			"	//@ assert x==3; \n" +
			"    } \n" +
			" \n" +
			"  public static void test03() { \n" +
			"      int[] x = null; \n" +
			"      //@ assert x instanceof Object; \n" +
			"  } \n" +
			" \n" +
			"  public static void test04() { \n" +
			"      int[] x = new int[3]; \n" +
			"      //@ assert x instanceof Object; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_295() {
			this.runNegativeTest(new String[] {
			testsPath + "A.java", 
			"// static methods with bodies \n" +
			" \n" +
			"public class A { \n" +
			" \n" +
			"  private static void testAssertionInBody1(int i) { \n" +
			"      //@ assert i/i == i/i; // expect: ZeroDiv \n" +
			"  } \n" +
			"   \n" +
			"  private static void testAssertionInBody2ForAll_div(int i) { \n" +
			"      // No range: \n" +
			"      //@ assert (\\forall int i; i != 0 ==> i/i == i/i); \n" +
			"      //@ assert (\\forall int i; i/i == i/i); // expect: ZeroDiv \n" +
			" \n" +
			"      // Trivial range: \n" +
			"      //@ assert (\\forall int i; true; i != 0 ==> i/i == i/i); \n" +
			"      //@ assert (\\forall int i; true; i/i == i/i); // expect: ZeroDiv \n" +
			" \n" +
			"      // Proper range: \n" +
			"      //@ assert (\\forall int i; i != 0; i/i == i/i); \n" +
			"      //@ assert (\\forall int i; i == 0 | i != 0; i/i == i/i); // expect: ZeroDiv \n" +
			"  } \n" +
			"   \n" +
			"   \n" +
			"  private static void testAssertionInBody2ForAll_deref(int i) { \n" +
			"      // No range: \n" +
			"      //@ assert (\\forall Object o; o != null ==> o.getClass() == o.getClass()); \n" +
			"      //@ assert (\\forall Object o; o.getClass() == o.getClass()); // expect: Null \n" +
			" \n" +
			"      // Range: \n" +
			"      //@ assert (\\forall Object o; o != null; o.getClass() == o.getClass()); \n" +
			"      //@ assert (\\forall Object o; true;      o.getClass() == o.getClass()); // expect: Null \n" +
			" \n" +
			"      // Unfortunately, ESC/Java2 does not yet support the following syntax ... \n" +
			"      //+@ assert (\\forall non_null Object o; o.getClass() == o.getClass()); \n" +
			"  } \n" +
			"   \n" +
			"  private static void testAssertionInBody2Exists(int i) { \n" +
			"      // No range: \n" +
			"      //@ assert (\\exists int i; i != 0 && i/i == i/i); // no IDC error, but unprovable by ATPs. \n" +
			"      //@ assert (\\exists int i; i/i == i/i); // expect: ZeroDiv \n" +
			" \n" +
			"      // Trivial range: \n" +
			"      //@ assert (\\exists int i; true; i != 0 && i/i == i/i); // no IDC error, but unprovable ... \n" +
			"      //@ assert (\\exists int i; true; i/i == i/i); // expect: ZeroDiv \n" +
			" \n" +
			"      // Proper range: \n" +
			"      //@ assert (\\exists int i; i != 0; i/i == i/i); // no IDC error, but unprovable by ATPs. \n" +
			"      //@ assert (\\exists int i; i == 0 | i != 0; i/i == i/i); // expect: ZeroDiv \n" +
			"  } \n" +
			" \n" +
			"    //@ requires i > 0 && (\\forall int j; j >= i; i/(j-i) == i/(j-i)); \n" +
			"    //@ requires i > 0 && (\\forall int j; j > i;  i/(j-i) == i/(j-i)); \n" +
			"    private static void testPre1(int i) { } \n" +
			" \n" +
			"    static int si; \n" +
			"    //@ static invariant (\\exists Object o; o.getClass() == o.getClass()) || si >= 0; \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_296() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"// Constructors with bodies \n" +
			" \n" +
			"public class C { \n" +
			"   \n" +
			"  public int i; \n" +
			" \n" +
			"  /*@ requires i>=0; \n" +
			"    @ ensures this.i == i/i; // divZero warning \n" +
			"    @*/ \n" +
			"  public C(int i) { \n" +
			"    this.i = 1; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ requires i>=0; \n" +
			"    @ ensures this.i == i+j+k; \n" +
			"    @*/ \n" +
			"  public C(int i, int j, int k) { \n" +
			"    this.i = i+j+k; \n" +
			"  } \n" +
			" \n" +
			"  /*@ ensures this.i == o.i/o.i; // null, divZero warning \n" +
			"    @*/ \n" +
			"  public C(C o) { \n" +
			"    this.i = 1; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ requires o.i >= 0;  // null warning \n" +
			"    @ ensures this.i == o.i; // no null warning - reported in precondition \n" +
			"    @*/ \n" +
			"  public C(C o, int i) { \n" +
			"    this.i = i; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ requires o.i >= 0; // null warning \n" +
			"    @ ensures this.i == o1.i; // null warning \n" +
			"    @*/ \n" +
			"  public C(C o, C o1, int i) { \n" +
			"    this.i = i; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i >= 0; \n" +
			"    @  ensures this.i == o.i; // null warning \n" +
			"    @*/ \n" +
			"  public C(C o, int i, int j) { \n" +
			"    this.i = i; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ exceptional_behavior \n" +
			"    @  requires i >= 0; \n" +
			"    @  signals (RuntimeException e) o.i/o.i == o.i/o.i; // null(o), divZero warnings \n" +
			"    @                                                   // invariant null(charArray.owner) warning \n" +
			"    @*/ \n" +
			"  public C(C o, int i, int j, int k) throws RuntimeException { \n" +
			"    throw new RuntimeException(); \n" +
			"  } // Postcondition not established warning \n" +
			"   \n" +
			"  /*@ normal_behavior  \n" +
			"    @  requires i>=0; \n" +
			"    @  ensures this.i == o.i+o.i; // no null warnings because of body \n" +
			"    @ also exceptional_behavior \n" +
			"    @  requires i<0; \n" +
			"    @  signals (RuntimeException e) o.i/o.i == 1; // null, divZero warning \n" +
			"    @                                             // invariant null(charArray.owner) warning \n" +
			"    @*/ \n" +
			"  public C(C o, C o1, int i, int j) throws RuntimeException { \n" +
			"    if (i<0) \n" +
			"      throw new RuntimeException(); \n" +
			"    this.i = o.i+o1.i; // null (o), null (o1) warnings \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_297() {
			this.runNegativeTest(new String[] {
			testsPath + "G.java", 
			"public class G { \n" +
			" \n" +
			"  /*@non_null */public int [] a; \n" +
			"   \n" +
			"  /*@ requires a.length >= 0;  // null(a) warning \n" +
			"    @ ensures this.a == a; \n" +
			"    @*/ \n" +
			"  public G(int [] a) { \n" +
			"    this.a = a; \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires a.length == this.a.length; \n" +
			"    @ ensures this.a[i] == \\old(this.a[i]+v); \n" +
			"    @*/ \n" +
			"  public void test0(int i, int v) { \n" +
			"    this.a[i]+=v; // idxNeg(i), idx2Large(i) \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires a.length == this.a.length; \n" +
			"    @ requires i>=0 && i<this.a.length; \n" +
			"    @ ensures this.a[i] == \\old(this.a[i]+v); \n" +
			"    @*/ \n" +
			"  public void test1(int i, int v) { \n" +
			"    this.a[i]+=v; // idxNeg(i), idx2Large(i) \n" +
			"  } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_298() {
			this.runNegativeTest(new String[] {
			testsPath + "Ghost.java", 
			"/** \n" +
			" ** This file tests that set does a writecheck on its target and that \n" +
			" ** ghost fields may have modifiers. \n" +
			" **/ \n" +
			" \n" +
			"// First test writable_if on ghost fields... \n" +
			"class WritableIf { \n" +
			"    //@ ghost public Object mono //@ writable_if mono==null \n" +
			"    //@ pure \n" +
			"    WritableIf() { \n" +
			"	Object newthing = new Object(); \n" +
			" \n" +
			"	//@ set mono = null;           // ok \n" +
			"	//@ set mono = newthing;       // ok, 1st time \n" +
			"	//@ set mono = newthing;       // error, 2nd time \n" +
			"    } \n" +
			"    //@ pure \n" +
			"    WritableIf(int x) { \n" +
			"	Object newthing = new Object(); \n" +
			" \n" +
			"	//@ set mono = null;           // ok \n" +
			"	//@ set mono = newthing;       // ok, 1st time \n" +
			"	//@ set mono = null;           // error, 2nd time \n" +
			"    } \n" +
			"} \n" +
			" \n" +
			"// Next, test non_null on ghost fields... \n" 
			}, "ERROR");
			}

			public void test_299() {
			this.runNegativeTest(new String[] {
			testsPath + "Ghost.java", 
			"class NonNull { \n" +
			"    //@ ghost public /*@non_null*/ Object foo \n" +
			"    //@ ghost public static /*@non_null*/ Object s \n" +
			"    //@ pure \n" +
			"    void foo(/*@non_null*/ Object x) { \n" +
			"	//@ assert foo != null \n" +
			"	//@ set foo = x        // ok since x != null \n" +
			"	//@ set foo = null     // error \n" +
			"	//@ set foo = foo      // ok since foo is known to be non-null \n" +
			"    } \n" +
			"    //@ pure \n" +
			"    void foo2(/*@non_null*/ Object x) { \n" +
			"	//@ assert s != null \n" +
			"	//@ set s = x        // ok since x != null \n" +
			"	//@ set s = null     // error \n" +
			"	//@ set s = s        // ok since s is known to be non-null \n" +
			"    } \n" +
			"} \n" +
			" \n" +
			" \n" +
			"// Next, test monitored_by on ghost fields... \n" 
			}, "ERROR");
			}

			public void test_300() {
			this.runNegativeTest(new String[] {
			testsPath + "Ghost.java", 
			"class MonitoredBy { \n" +
			"    public Object mutex; \n" +
			" \n" +
			"    //@ ghost public Object x //@ monitored_by mutex \n" +
			"    //@ pure \n" +
			"    void foo(Object foo) { \n" +
			"	//@ assert x==x        // ok: annotations don't \"read\" variables... \n" +
			"	//@ set x = foo         // error \n" +
			" \n" +
			"	synchronized (mutex) { \n" +
			"	    //@ set x = foo     // ok since hold mutex \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_301() {
			this.runNegativeTest(new String[] {
			testsPath + "Cliteral.java", 
			"/** \n" +
			" ** This class tests the translation of class literals.  See front end \n" +
			" ** test fe/test100 for tests of parsing and typechecking of class \n" +
			" ** literals (a 1.1 feature) \n" +
			" **/ \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_302() {
			this.runNegativeTest(new String[] {
			testsPath + "Cliteral.java", 
			"class Cliteral { \n" +
			"    void specTest() { \n" 
			}, "ERROR");
			}

			public void test_303() {
			this.runNegativeTest(new String[] {
			testsPath + "Cliteral.java", 
			"	//@ assert \\TYPE.class == \\TYPE.class \n" 
			}, "ERROR");
			}

			public void test_304() {
			this.runNegativeTest(new String[] {
			testsPath + "Cliteral.java", 
			"	//@ assert void[].class == void[].class \n" 
			}, "ERROR");
			}

			public void test_305() {
			this.runNegativeTest(new String[] {
			testsPath + "Cliteral.java", 
			"	//@ assert Cliteral.class == Cliteral.class \n" 
			}, "ERROR");
			}

			public void test_306() {
			this.runNegativeTest(new String[] {
			testsPath + "Cliteral.java", 
			"	//@ assert Cliteral[].class == Cliteral[].class \n" 
			}, "ERROR");
			}

			public void test_307() {
			this.runNegativeTest(new String[] {
			testsPath + "Cliteral.java", 
			"	//@ assert Cliteral[][].class == Cliteral[][].class \n" +
			"    } \n" +
			" \n" +
			"    void typingTest() { \n" 
			}, "ERROR");
			}

			public void test_308() {
			this.runNegativeTest(new String[] {
			testsPath + "Cliteral.java", 
			"	//@ assert void.class != null \n" +
			"	//@ assert \\typeof(int.class) == \\type(Class) \n" +
			"    } \n" +
			" \n" +
			"    public static void main(String[] args) { \n" +
			" \n" +
			"	// void . class: \n" +
			"	out(void.class); \n" +
			" \n" +
			"	// <java primitive type> . class: \n" +
			"	out(int.class); \n" +
			"	out(short.class); \n" +
			"	out(byte.class); \n" +
			"	out(boolean.class); \n" +
			"	out(char.class); \n" +
			"	out(float.class); \n" +
			"	out(double.class); \n" +
			"	out(long.class); \n" +
			" \n" +
			"	// <java primitive type> []* . class: \n" +
			"	out(int.class); \n" +
			"	out(int[].class); \n" +
			"	out(int[][].class); \n" +
			"	out(int[][][].class); \n" +
			"	out(void[].class); \n" +
			" \n" +
			"	// <typename> . class: \n" +
			"	out(String.class); \n" +
			"	out(java.lang.Math.class); \n" +
			"	out(Cliteral.class); \n" +
			" \n" +
			"	// <typename> []* . class: \n" +
			"	out(String[].class); \n" +
			"	out(java.lang.Math[].class); \n" +
			"	out(String[][].class); \n" +
			"	out(java.lang.Math[][].class); \n" +
			"    } \n" +
			" \n" +
			"    void stillWorking() { \n" +
			"	Object[] objects = null; \n" +
			"	Object[] moreObjects = null; \n" +
			"    } \n" +
			" \n" +
			"    static void out(/*@ non_null */ Class c) { \n" +
			"	System.out.println(c); \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_309() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			"  boolean x, y; \n" +
			" \n" +
			"  /*@ requires x \n" +
			"          && y; */ \n" +
			"  void m0() { \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires x && y; \n" +
			"        */ \n" +
			"  void m1() { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x && y \n" +
			"  void m2() { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x && y; \n" +
			"  void m3() { \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires x && y */ \n" +
			"  void m4() { \n" +
			"  } \n" +
			" \n" +
			"  /*@ non_null \n" +
			"   */ int[] a = new int[25]; \n" +
			" \n" +
			"  /** \"<esc> monitored_by this \n" +
			"      , this.a </esc> */ \n" +
			"  Object b; \n" +
			" \n" +
			"  /** \"<esc> monitored \n" +
			"      </esc> */ \n" +
			"  Object c; \n" +
			" \n" +
			"  void caller0(int t) { \n" +
			"    switch (t) { \n" +
			"      case 0:  m0(); break; \n" +
			"      case 1:  m1(); break; \n" +
			"      case 2:  m2(); break; \n" +
			"      case 3:  m3(); break; \n" +
			"      case 4:  m4(); break; \n" +
			"      case 5:  a = null; break; \n" +
			"      case 6: { /*@ uninitialized \n" +
			"		       non_null */ int[] a = null; a = a; } break; \n" +
			"      case 7:  b = a; break; \n" +
			"      case 8:  c = a; break; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"/*@requires s==\"h</esc>\\\"</esc>'</esc>\\n\\034\"+'c'+'\\''+\"</esc>\" \n" +
			"        */ \n" +
			"  void p0(String s) { \n" +
			"  } \n" +
			" \n" +
			"  /** //   <esc> requires b != null \n" +
			"              </esc> */ \n" +
			"  void p1() { \n" +
			"  } \n" +
			" \n" +
			"  /** \"//\"   <esc> requires b != null \n" +
			"              </esc> */ \n" +
			"  void p2() { \n" +
			"  } \n" +
			" \n" +
			"  //@ /* h'\\\\\\\\\\ ;'' a cmnt\" y */ ensures \\result < -1 \n" +
			"  //@ requires true|\"*/\\\"\"==\"</esc>\"; ensures \\result > -7 \n" +
			"  int caller1(int t) { \n" +
			"    switch (t) { \n" +
			"      case -10: case -2: case -1:  return t; \n" +
			"      case 0:  p0(null); break; \n" +
			"      case 1:  p1(); break; \n" +
			"      case 2:  p2(); break; \n" +
			"      case 3:  tz += 20; break; \n" +
			"      case 9:  /** <esc>unreachable \n" +
			"		   ; </esc>*/ break; \n" +
			"    } \n" +
			"    return -5; \n" +
			"  } \n" +
			" \n" +
			"  int tz = 20 /* *// 2; /*@ invariant \n" +
			"		tz < 100; */ \n" +
			" \n" +
			"  //@ invariant tz>=0 /* */*0; invariant tz==10||tz%3==0 \n" +
			" \n" +
			"  /** <esc>ensures 0 <// comment goes here \n" +
			"          \\result    </esc> */ \n" +
			"  // The next test case will place the ellipsis in a slightly awkward place \n" +
			"  /*@ ensures c // why \"c\" one wonders \n" +
			"              != null; */ \n" +
			"  int q(int t) { \n" +
			"    return t; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_310() {
			this.runNegativeTest(new String[] {
			testsPath + "ghost.java", 
			"class Ghost21 { \n" +
			"  //@ ghost public int i; \n" +
			"  //@ghost public boolean b; \n" +
			" \n" +
			" //@invariant b && (b == true) && (i > 0); \n" +
			" \n" +
			"Ghost21() { \n" +
			"  //@set i= 6;  \n" +
			"  //@set b= true; \n" +
			"} \n" +
			" \n" +
			"void m() { \n" +
			"//@ assert (i > -1) && b; \n" +
			" \n" +
			"} \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_311() {
			this.runNegativeTest(new String[] {
			testsPath + "bag.java", 
			"class Bag { \n" +
			"  int[] a; \n" +
			"  int n; \n" +
			" \n" +
			"  Bag(int[] input) { \n" +
			"    n = input.length; \n" +
			"    a = new int[n]; \n" +
			"    System.arraycopy(input, 0, a, 0, n); \n" +
			"  } \n" +
			" \n" +
			"  int extractMin() { \n" +
			"    int m = Integer.MAX_VALUE; \n" +
			"    int mindex = 0; \n" +
			"    for (int i = 1; i <= n; i++) { \n" +
			"      if (a[i] < m) { \n" +
			"        mindex = i; \n" +
			"        m = a[i]; \n" +
			"      } \n" +
			"    } \n" +
			"    n--; \n" +
			"    a[mindex] = a[n]; \n" +
			"    return m; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_312() {
			this.runNegativeTest(new String[] {
			testsPath + "helper.java", 
			" \n" +
			"class C { \n" +
			"    int i; \n" +
			"     \n" +
			"    void m0(Integer l) { \n" +
			"	int q = l.intValue(); \n" +
			"	m1(l); \n" +
			"    } \n" +
			" \n" +
			"    void m1(Integer k) { \n" +
			"	m2(k); \n" +
			"    } \n" +
			" \n" +
			"    /*@ helper */ private void m2(Integer j) { \n" +
			"	i = j.intValue(); \n" +
			"    } \n" +
			" \n" +
			"	 \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_313() {
			this.runNegativeTest(new String[] {
			testsPath + "nowarn.java", 
			" \n" +
			"class C { \n" +
			"    public int i; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_314() {
			this.runNegativeTest(new String[] {
			testsPath + "nowarn.java", 
			"class D { \n" +
			"    int m(C c) { \n" +
			"	return c.i; //@ nowarn Null \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_315() {
			this.runNegativeTest(new String[] {
			testsPath + "skip.java", 
			" \n" +
			"/* This simple code shows the differences in our three inlining schemes, \n" +
			"   obtained by different combinations of the last three args to the _call_ \n" +
			"   routine: \n" +
			" \n" +
			"   A) inline a call without checking (true, false, true) \n" +
			"   B) inline an artificial call (true, true, true) \n" +
			"   C) inline a call with checking (true, true, false) \n" +
			" \n" +
			"   We get three different warnings on method _p_ below, in the three cases above. \n" +
			"*/ \n" +
			" \n" +
			"class C { \n" +
			"    int i; \n" +
			" \n" +
			"    int p(C c) { \n" +
			"	return m(c); \n" +
			"    } \n" +
			" \n" +
			"    //@ requires c.i > 0 \n" +
			"    int m(C c) { \n" +
			"	i = c.i; \n" +
			"	return i; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_316() {
			this.runNegativeTest(new String[] {
			testsPath + "postcondition.java", 
			" \n" +
			"class C { \n" +
			"    int i; \n" +
			"     \n" +
			"    int m0(int l) { \n" +
			"	return m1(l); \n" +
			"    } \n" +
			" \n" +
			"    //@ requires k == 5 \n" +
			"    //@ ensures \\result == 5 \n" +
			"    int m1(int k) { \n" +
			"	return k; \n" +
			"    } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_317() {
			this.runNegativeTest(new String[] {
			testsPath + "this.java", 
			" \n" +
			"class T { \n" +
			"    int x; \n" +
			"     \n" +
			"    T() { \n" +
			"    } \n" +
			" \n" +
			"    //@ requires t != this \n" +
			"    //@ requires t != null \n" +
			"    //@ ensures this.x == 3 \n" +
			"    void m(T t) { \n" +
			"	x = 3; \n" +
			"	t.set(); \n" +
			"    } \n" +
			" \n" +
			"    void set() { \n" +
			"	x = 4; \n" +
			"    } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_318() {
			this.runNegativeTest(new String[] {
			testsPath + "flags.java", 
			" \n" +
			"class C { \n" +
			"    int i; \n" +
			"     \n" +
			"    void m0(Integer l) { \n" +
			"	int q = l.intValue(); \n" +
			"	m1(l); \n" +
			"    } \n" +
			" \n" +
			"    void m1(Integer k) { \n" +
			"	m2(k); \n" +
			"    } \n" +
			" \n" +
			"    private void m2(Integer j) { \n" +
			"	i = j.intValue(); \n" +
			"    } \n" +
			" \n" +
			"	 \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_319() {
			this.runNegativeTest(new String[] {
			testsPath + "postcondition2.java", 
			" \n" +
			"class C { \n" +
			"    C() { \n" +
			"    } \n" +
			" \n" +
			"    //@ ensures \\result > 0 \n" +
			"    int m(int j) { \n" +
			"	return j; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_320() {
			this.runNegativeTest(new String[] {
			testsPath + "StackCheck.java", 
			"		 \n" +
			"// DO NOT EDIT THIS FILE		 \n" +
			"// Only edit Stack.java		 \n" +
			"		 \n" +
			"/**		 \n" +
			" * StackCheck is a class which calls Stack and verifies that the		 \n" +
			" * written specification is sufficient.		 \n" +
			" **/		 \n"
			}, "ERROR");
			}

			public void test_321() {
			this.runNegativeTest(new String[] {
			testsPath + "StackCheck.java", 
			"public class StackCheck		 \n" +
			"{		 \n" +
			"		 \n" +
			"  /**		 \n" +
			"   * Helper method to generate elements to place in the queue.		 \n" +
			"   * Stack elements are never null.		 \n" +
			"   **/		 \n" +
			"  private static Object element()		 \n" +
			"  //@ ensures \\result != null;		 \n" +
			"  {		 \n" +
			"    return new Object();		 \n" +
			"  }		 \n" +
			"		 \n" +
			"  /**		 \n" +
			"   * Check that legal call sequences to the constructor and push throw		 \n" +
			"   * no runtime exceptions.		 \n" +
			"   **/		 \n" +
			"  public static void checkConstructor() {		 \n" +
			"    Stack s;		 \n" +
			"    s = new Stack(1);		 \n" +
			"    s.push(element());		 \n" +
			"    s = new Stack(2);		 \n" +
			"    s.push(element());		 \n" +
			"    s.push(element());		 \n" +
			"  }		 \n" +
			"		 \n" +
			"  /**		 \n" +
			"   * Check that the isEmpty specification is correctly related to the		 \n" +
			"   * push specification.		 \n" +
			"   **/		 \n" +
			"  public static void checkIsEmpty() {		 \n" +
			"    Stack s = new Stack(2);		 \n" +
			"		 \n" +
			"	// new stack should be empty		 \n" +
			"    //@ assert s.isEmpty();		 \n" +
			"  		 \n" +
			"    s.push(element());		 \n" +
			"	// 1-elt stack should not be empty		 \n" +
			"    //@ assert !s.isEmpty();		 \n" +
			"		 \n" +
			"    s.push(element());		 \n" +
			"	// 2-elt stack should not be empty		 \n" +
			"    //@ assert !s.isEmpty();		 \n" +
			"  }		 \n" +
			"		 \n" +
			"  /**		 \n" +
			"   * Check that the isFull specification is correctly related to the		 \n" +
			"   * push specification.		 \n" +
			"   **/		 \n" +
			"  public static void checkIsFull() {		 \n" +
			"    Stack s = new Stack(2);		 \n" +
			"    		 \n" +
			"	// new stack should not be full		 \n" +
			"    //@ assert !s.isFull();		 \n" +
			"   		 \n" +
			"    s.push(element());		 \n" +
			"	// 1-elt stack should not be full		 \n" +
			"    //@ assert !s.isFull();		 \n" +
			"   		 \n" +
			"    s.push(element());		 \n" +
			"	// 2-elt stack should be full		 \n" +
			"    //@ assert s.isFull();		 \n" +
			"  }		 \n" +
			"		 \n" +
			"  /**		 \n" +
			"   * Check that top returns null iff the queue is empty.		 \n" +
			"   **/		 \n" +
			"  public static void checkTop() {		 \n" +
			"    Stack s = new Stack(2);		 \n" +
			"  		 \n" +
			"	// Top of new stack should be null		 \n" +
			"    //@ assert s.top() == null;		 \n" +
			"   		 \n" +
			"    s.push(element());		 \n" +
			"	// Top of 1-elt stack should be non-null		 \n" +
			"    //@ assert s.top() != null;		 \n" +
			"		 \n" +
			"  }		 \n" +
			"		 \n" +
			"  /**		 \n" +
			"   * Check that legal call sequences to the constructor, push, and pop		 \n" +
			"   * throw no runtime exceptions.		 \n" +
			"   **/		 \n" +
			"  public static void checkPop() {		 \n" +
			"    Stack s = new Stack(2);	 \n" +
			"  		 \n" +
			"    s.push(element());		 \n" +
			"    s.pop();		 \n" +
			"    		 \n" +
			"    s.push(element());		 \n" +
			"    s.push(element());		 \n" +
			"    s.pop();		 \n" +
			"    s.pop();		 \n" +
			"  }		 \n" +
			"		 \n" +
			"}		 \n" 
			}, "ERROR");
			}

			public void test_322() {
			this.runNegativeTest(new String[] {
			testsPath + "Stack.java", 
			"/**		 \n" +
			" * Name: Ryan Miller		 \n" +
			" * AndrewID: rdmiller		 \n" +
			" * TimeSpent: 7:25 -		 \n" +
			"		*/		 \n" +
			"		 \n" +
			"/**		 \n" +
			" * Array-based implementation of the stack.		 \n" +
			" */		 \n" +
			"public class Stack		 \n" +
			"{		 \n" +
			"		 \n" +
			"    /**		 \n" +
			"     * Construct the stack.		 \n" +
			"     */		 \n" +
			"	/*@		 \n" +
			"	  @ requires capacity > 0;		 \n" +
			"	  @ ensures theArray != null && topOfStack == -1;		 \n" +
			"	  @*/		 \n" +
			"    public Stack( int capacity )		 \n" +
			"    {		 \n" +
			"        theArray = new Object[ capacity ];		 \n" +
			"        topOfStack = -1;		 \n" +
			"        //@ set theArray.owner = this;		 \n" +
			"    }		 \n" +
			"		 \n" +
			"    /**		 \n" +
			"     * Test if the stack is logically empty.		 \n" +
			"     */		 \n" +
			"    /*@ 		 \n" +
			"      @ pure		 \n" +
			"      @ ensures \\result == (topOfStack == -1);		 \n" +
			"      @*/		 \n" +
			"    public boolean isEmpty( )		 \n" +
			"    {		 \n" +
			"        return topOfStack == -1;		 \n" +
			"    }		 \n" +
			"		 \n" +
			"    /**		 \n" +
			"     * Test if the stack is logically full.		 \n" +
			"     */		 \n" +
			"    /*@ pure		 \n" +
			"      @ ensures \\result == (topOfStack >= theArray.length - 1);		 \n" +
			"      @*/		 \n" +
			"    public boolean isFull( )		 \n" +
			"    {		 \n" +
			"        return topOfStack >= theArray.length - 1;		 \n" +
			"    }		 \n" +
			"		 \n" +
			"    /**		 \n" +
			"     * Get the most recently inserted item in the stack.		 \n" +
			"     * Does not alter the stack.		 \n" +
			"     */		 \n" +
			"    /*@ pure */		 \n" +
			"    public Object top( )		 \n" +
			"    {		 \n" +
			"        if( isEmpty( ) )		 \n" +
			"            return null;		 \n" +
			"        //@ assert topOfStack >= 0;		 \n" +
			"        return theArray[ topOfStack ];		 \n" +
			"    }		 \n" +
			"		 \n" +
			"    /**		 \n" +
			"     * Remove the most recently inserted item from the stack.		 \n" +
			"     */		 \n" +
			"    /*@ 		 \n" +
			"      @ requires !isEmpty();		 \n" +
			"      @ ensures topOfStack >= -1;		 \n" +
			"      @ ensures (\\forall int j; (0 <= j && j < topOfStack)		 \n" +
			"		         ==> theArray[j] == \\old(theArray[j]));		 \n" +
			"      @ modifies this.topOfStack, this.theArray[*];		 \n" +
			"      @*/		 \n" +
			"    public void pop( )		 \n" +
			"    {		 \n" +
			"        theArray[ topOfStack-- ] = null;		 \n" +
			"    }		 \n" +
			"		 \n" +
			"    /**		 \n" +
			"     * Insert a new item into the stack, if not already full.		 \n" +
			"     */		 \n" +
			"    /*@ 		 \n" +
			"      @ requires !isFull();		 \n" +
			"      @ ensures topOfStack >= 0;		 \n" +
			"      @ ensures (\\forall int j; (0 <= j && j < \\old(topOfStack))		 \n" +
			"				 ==> theArray[j] == \\old(theArray[j]));		 \n" +
			"      @ modifies this.topOfStack, this.theArray[*];		 \n" +
			"      @*/		 \n" +
			"    public void push( Object x )		 \n" +
			"    {		 \n" +
			"        theArray[ ++topOfStack ] = x;		 \n" +
			"    }		 \n" +
			"		 \n" +
			"		 \n" +
			"    /*@ invariant \\typeof(this.theArray) == \\type(java.lang.Object[]); */		 \n" +
			"    /*@ invariant theArray.owner == this; */		 \n" +
			"    /*@ invariant theArray != null; */		 \n" +
			"    /* spec_public */ private Object [ ] theArray;		 \n" +
			"		 \n" +
			"    /*@ invariant -1 <= topOfStack && topOfStack < theArray.length; */		 \n" +
			"    /* spec_public */ private int        topOfStack;		 \n" +
			"}		 \n" 
			}, "ERROR");		}

			public void test_323() {
			this.runNegativeTest(new String[] {
			testsPath + "arrayinit.java", 
			"class C { \n" +
			" \n" +
			"  void m() { \n" +
			" \n" +
			"    boolean b = (1<2); \n" +
			"    //@ assert b==true; \n" +
			" \n" +
			"    boolean[] bs = { true, false }; \n" +
			" \n" +
			"    //@ assert bs.length == 2; \n" +
			"    //@ assert bs[0] == true; \n" +
			"    //@ assert bs[1] == false; \n" +
			" \n" +
			"    bs = new boolean[] { false, true, false }; \n" +
			" \n" +
			"    //@ assert bs.length == 3; \n" +
			"    //@ assert bs[0] == false; \n" +
			"    //@ assert bs[1] == true; \n" +
			"    //@ assert bs[2] == false; \n" +
			" \n" +
			"    boolean[][] bs2; \n" +
			"    bs2 = new boolean[][] { { true, false}, {false}, {} }; \n" +
			"    //@ assert bs2.length == 3; \n" +
			"    //@ assert bs2[0].length == 2; \n" +
			"    //@ assert bs2[0][0] == true; \n" +
			"    //@ assert bs2[0][1] == false; \n" +
			"    //@ assert bs2[1].length == 1; \n" +
			"    //@ assert bs2[1][0] == false; \n" +
			"    //@ assert bs2[2].length == 0; \n" +
			" \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_324() {
			this.runNegativeTest(new String[] {
			testsPath + "UnaryPlus.java", 
			"class UnaryPlus { \n" +
			"  //@ ensures \\result == 1 && \\result == -(-1); \n" +
			"  int m() { \n" +
			"    int x = +1; \n" +
			"    return x; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_325() {
			this.runNegativeTest(new String[] {
			testsPath + "divmod.java", 
			" \n" +
			"class divmod { \n" +
			"  public static void m1() { \n" +
			"    int y = 4 / 2; \n" +
			"  } \n" +
			" \n" +
			"  public static void m2() { \n" +
			"    int y = 4 % 2; \n" +
			"  } \n" +
			" \n" +
			"  public static void m3() { \n" +
			"    int y = 4; \n" +
			"    y /= 2; \n" +
			"  } \n" +
			" \n" +
			"  public static void m4() { \n" +
			"    int y = 4; \n" +
			"    y %= 2; \n" +
			"  } \n" +
			" \n" +
			"  public static void m5() { \n" +
			"    int y = 4; \n" +
			"    int x = (y %= 2) + y; \n" +
			"    x = x + (x /= 2); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_326() {
			this.runNegativeTest(new String[] {
			testsPath + "setfield.java", 
			" \n" +
			"class setfieldsuper { \n" +
			"  int instancevar; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_327() {
			this.runNegativeTest(new String[] {
			testsPath + "setfield.java", 
			"class setfield extends setfieldsuper { \n" +
			"  static int classvar; // Used for testing by fieldref class \n" +
			"  int[] arrayvar; \n" +
			" \n" +
			"  public static void m1(setfield o) { \n" +
			"    //@ assume o != null; \n" +
			"    o.classvar = 10; \n" +
			"    o.instancevar = 10; \n" +
			"    // o.instancevar += 5; \n" +
			"    //@ assert 20 == o.instancevar + classvar; \n" +
			"  } \n" +
			" \n" +
			"  public static void m2(setfield o) { \n" +
			"    //@ assume o != null; \n" +
			"    //@ assume o.arrayvar != null; \n" +
			"    //@ assume o.arrayvar.length == 10; \n" +
			"    o.arrayvar[9] = 10; \n" +
			"    //@ assert 10 == o.arrayvar[9]; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_328() {
			this.runNegativeTest(new String[] {
			testsPath + "newarray.java", 
			" \n" +
			"public class newarray { \n" +
			"  //@ requires n >= 0; \n" +
			"  void m1(int n) { \n" +
			"    int[] ai = new int[n]; \n" +
			"    long[] al = new long[n]; \n" +
			"    char[] ac = new char[n]; \n" +
			"    byte[] ab = new byte[n]; \n" +
			"    short[] as = new short[n]; \n" +
			" \n" +
			"    // double[] ad = new double[n]; \n" +
			"    // float[] af = new float[n]; \n" +
			" \n" +
			"    boolean[] abool = new boolean[n]; \n" +
			" \n" +
			"    Object[] aobj = new Object[n]; \n" +
			"    String[] astr = new String[n]; \n" +
			" \n" +
			"    int[][] aai = new int[n][]; \n" +
			"    Object[][] aaobj = new Object[n][]; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires n >= 0 ; \n" +
			"  void m2(int n) { \n" +
			"    int[][] aai = new int[n][n]; \n" +
			"    long[][][] aaal = new long[n][n][]; \n" +
			"    byte[][][] aaab = new byte[n][n][n]; \n" +
			"    boolean[][][][] aaaabool = new boolean[n][n][n][n]; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires n >= 0 ; \n" +
			"  void m3(int n) { \n" +
			"    Object[][][][] aaaaobj = new Object[n++][n++][n++][n++]; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires n >= 0 ; \n" +
			"  void m4(int n) { \n" +
			"    boolean[] abool = new boolean[n]; \n" +
			"    //@ assert abool.length == n; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires n >= 0 ; \n" +
			"  void m5(int n) { \n" +
			"    boolean[][] aabool = new boolean[n][n]; \n" +
			"    //@ assert aabool[1].length == n; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_329() {
			this.runNegativeTest(new String[] {
			testsPath + "cast.java", 
			" \n" +
			"class Cast { \n" +
			" \n" +
			"  void m1(Object o) { \n" +
			"    //@ assume o instanceof String; \n" +
			"    String s = (String)o; \n" +
			"  } \n" +
			" \n" +
			"  void m2(Object o) { \n" +
			"    //@ assume \\typeof(o) <: \\type(String); \n" +
			"    String s = (String)o; \n" +
			"  } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_330() {
			this.runNegativeTest(new String[] {
			testsPath + "fieldref.java", 
			" \n" +
			"class fieldsuper { \n" +
			"  int instancevar; \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_331() {
			this.runNegativeTest(new String[] {
			testsPath + "fieldref.java", 
			"class fieldref extends fieldsuper { \n" +
			"  static int classvar; // Used for testing by fieldref class \n" +
			" \n" +
			"  public static int m1(fieldref o) { \n" +
			"    //@ assume o != null; \n" +
			"    return fieldref.classvar + o.classvar + o.instancevar; \n" +
			"  } \n" +
			" \n" +
			"  public int m2() { \n" +
			"    /*@ assume this != null; */ // Shouldn't be needed!! \n" +
			"    return instancevar + this.instancevar + super.instancevar; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_332() {
			this.runNegativeTest(new String[] {
			testsPath + "arrayref.java", 
			" \n" +
			"class arrayref { \n" +
			"  public static int m1(int[] a) { \n" +
			"    //@ assume a != null; \n" +
			"    //@ assume a.length == 10; \n" +
			"    return a[1]; \n" +
			"  } \n" +
			" \n" +
			"  public static int m2(int[] a) { \n" +
			"    //@ assume a != null; \n" +
			"    //@ assume a.length == 10; \n" +
			"    int x = 1; \n" +
			"    return a[x] + a[x += 1]; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_333() {
			this.runNegativeTest(new String[] {
			testsPath + "gets.java", 
			"class gets { \n" +
			"    int m() { \n" +
			"	int i; \n" +
			"	i= 6; \n" +
			"	/*@ assert i == 6; */ \n" +
			"	return i; \n" +
			"    } \n" +
			" \n" +
			"    void n() { \n" +
			"	int i, j; \n" +
			"        j= 6; \n" +
			"	i= j + (j= 2); \n" +
			"	/*@ assert i == 8; */ \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_334() {
			this.runNegativeTest(new String[] {
			testsPath + "inc.java", 
			" \n" +
			"public class inc { \n" +
			"  public void m1() { \n" +
			"    int x = 0; \n" +
			"    x++; \n" +
			"    //@ assert x == 1; \n" +
			"  } \n" +
			" \n" +
			"  public void m2() { \n" +
			"    int x = 0; \n" +
			"    ++x; \n" +
			"    //@ assert x == 1; \n" +
			"  } \n" +
			" \n" +
			"  public void m3() { \n" +
			"    int x = 0; \n" +
			"    x--; \n" +
			"    //@ assert x == -1; \n" +
			"  } \n" +
			" \n" +
			"  public void m4() { \n" +
			"    int x = 0; \n" +
			"    --x; \n" +
			"    //@ assert x == -1; \n" +
			"  } \n" +
			" \n" +
			"  public void m5() { \n" +
			"    int x = 0; \n" +
			"    int y = x++; \n" +
			"    //@ assert y == 0; \n" +
			"  } \n" +
			" \n" +
			"  public void m6() { \n" +
			"    int x = 0; \n" +
			"    int y = ++x; \n" +
			"    //@ assert y == 1; \n" +
			"  } \n" +
			" \n" +
			"  public void m7() { \n" +
			"    int x = 0; \n" +
			"    int y = x--; \n" +
			"    //@ assert y == 0; \n" +
			"  } \n" +
			" \n" +
			"  public void m8() { \n" +
			"    int x = 0; \n" +
			"    int y = --x; \n" +
			"    //@ assert y == -1; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_335() {
			this.runNegativeTest(new String[] {
			testsPath + "getsplus.java", 
			"class getsplus { \n" +
			"    int m() { \n" +
			"	int i; \n" +
			"	i= 6; \n" +
			"	i+= 6; \n" +
			"	/** assert i == 12; */ \n" +
			"	return i; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_336() {
			this.runNegativeTest(new String[] {
			testsPath + "PreppingGhosts.java", 
			"/** \n" +
			" ** Verify that ghost fields are prepped before they are used \n" +
			" **  \n" +
			" **/ \n" +
			" \n" +
			"class PreppingGhosts1 { \n" +
			"    //@ invariant Ghosty1.x == null \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_337() {
			this.runNegativeTest(new String[] {
			testsPath + "PreppingGhosts.java", 
			"class Ghosty1 { \n" +
			"    //@ ghost static public Object x \n" +
			"} \n" +
			" \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_338() {
			this.runNegativeTest(new String[] {
			testsPath + "PreppingGhosts.java", 
			"class PreppingGhosts2 { \n" +
			"    //@ invariant Ghosty2.y == null         // error \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_339() {
			this.runNegativeTest(new String[] {
			testsPath + "PreppingGhosts.java", 
			"class Ghosty2 { \n" +
			"    //@ ghost static public Nonexistent y \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_340() {
			this.runNegativeTest(new String[] {
			testsPath + "ghost.java", 
			"class Ghost98 { \n" +
			"  //@ ghost public Ghost98 link; \n" +
			"  //@ghost public boolean b; \n" +
			" \n" +
			" //@invariant b && (b == true) && (this == link); \n" +
			" \n" +
			"Ghost98() { \n" +
			"  //@set link= this;  \n" +
			"  //@set b= true; \n" +
			"  if (this.m()) { \n" +
			"    //@set link= this; \n" +
			"  } \n" +
			"  else { \n" +
			"    //@set link= null; \n" +
			"} \n" +
			"} \n" +
			" \n" +
			"//@ requires true; \n" +
			"//@ ensures \\result == this.b \n" +
			"boolean m() \n" +
			"{ }  //@nowarn Post \n" +
			" \n" +
			" \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_341() {
			this.runNegativeTest(new String[] {
			testsPath + "Test.java", 
			"class Test { \n" +
			" \n" +
			"    static int x, y; \n" +
			" \n" +
			"    //@ invariant true   // error \n" +
			"    //@ axiom true \n" +
			" \n" +
			"    //@ invariant x == 0 \n" +
			"    //@ invariant y == 0 \n" +
			" \n" +
			"    //@ invariant x == y; \n" +
			"    //@ invariant x == Foo.y \n" +
			" \n" +
			"    //@ invariant (\\forall int x; x == 0)  // error \n" +
			"    //@ invariant (\\forall Test t; t == null) // error \n" +
			"    //@ invariant (\\forall Test t; t.x == 0)  \n" +
			" \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_342() {
			this.runNegativeTest(new String[] {
			testsPath + "Test.java", 
			"class Foo { \n" +
			" \n" +
			"    static int x, y; \n" +
			" \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_343() {
			this.runNegativeTest(new String[] {
			testsPath + "StmtPragmas1.java", 
			" \n" +
			"// Tests for resolution and typechecking of pragmas \n" +
			" \n" +
			"public abstract class StmtPragmas1 { \n" +
			"  static int count; \n" +
			"  static { \n" +
			"    /*@ assume 0 <= count */ \n" +
			"    if (count < 0) { \n" +
			"      /*@ unreachable; */ \n" +
			"      throw new RuntimeException(); \n" +
			"    } \n" +
			"    count++; \n" +
			"    /*@ assert 0 <= count; */ \n" +
			"  } \n" +
			" \n" +
			"  public static int find(int[] a, int el) \n" +
			"    /*@ requires a != null */ \n" +
			"    /*@ requires (exists int i; (0 <= i && i < a.length) & a[i] == el) */ \n" +
			"    /*@ requires (forall int i; (0 <= i-1 && i-1 < a.length) ==> a[i-1] < a[i]) */ \n" +
			"    /*@ ensures (0 <= RES && RES < a.length) & a[RES] == el; */ \n" +
			"  { \n" +
			"    int lo = 0, hi = a.length-1; \n" +
			"    if (a[lo] == el) return lo; \n" +
			"    if (a[hi] == el) return hi; \n" +
			"    for(int i = 0; i <= hi; i++) { \n" +
			"      /*@ loop_invariant lo < hi */ \n" +
			"      /*@ loop_invariant (0 <= lo && lo < a.length)  \n" +
			"	               & (0 <= hi && hi < a.length) */ \n" +
			"      /*@ loop_invariant a[lo] < el & el < a[hi] */ \n" +
			"      int mid = lo + (hi - lo)/2; \n" +
			"      if (el == a[mid]) return mid; \n" +
			"      else if (el < a[mid]) hi = mid; \n" +
			"      else lo = mid; \n" +
			"    } \n" +
			"    /*@ unreachable */ \n" +
			"    return -1; \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_344() {
			this.runNegativeTest(new String[] {
			testsPath + "MethodCall.java", 
			" \n" +
			"public class MethodCall { \n" +
			" \n" +
			"  //@ ensures false; \n" +
			"  static MethodCall loopForever() { \n" +
			"    while (true) \n" +
			"      ; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires r0 != null && r1 != null; \n" +
			"  static void pairaNonnulls(Object r0, Object r1) { \n" +
			"  } \n" +
			" \n" +
			"  void m0_ok(MethodCall mc) { \n" +
			"    if (mc != null) { \n" +
			"      mc.m0_ok(mc = null);      // okay \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m1_fail(MethodCall mc) { \n" +
			"    (mc = null).m1_fail(mc);      // null dereference \n" +
			"  } \n" +
			" \n" +
			"  void m2_ok(MethodCall mc) { \n" +
			"    mc = null; \n" +
			"    mc.m2_ok(loopForever());    // does not generate error, since \"loopForever\" doesn't return \n" +
			"  } \n" +
			" \n" +
			"  void m3_ok(MethodCall mc) { \n" +
			"    if (mc != null) { \n" +
			"      mc.m2_ok(loopForever()); \n" +
			"      // next line does not generate error, since \"loopForever\" doesn't return \n" +
			"      //@ assert false; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m4_ok() { \n" +
			"    /********  the following line currently crashes the checker \n" +
			"    MethodCall.m4_ok();  // this is not allowed in Java (can't make static \n" +
			"                         // reference to instance method) \n" +
			"    *********/ \n" +
			"  } \n" +
			" \n" +
			"  static void m5_ok() { \n" +
			"    MethodCall.m5_ok(); \n" +
			"    m5_ok(); \n" +
			"  } \n" +
			" \n" +
			"  void m6_ok(MethodCall mc) { \n" +
			"    // Note that \"m5_ok\" is static, so \"mc\" will be ignored, and it doesn't \n" +
			"    // matter if \"mc\" is null. \n" +
			"    mc.m5_ok();   \n" +
			"  } \n" +
			" \n" +
			"  MethodCall f; \n" +
			"   \n" +
			"  void m7_fail(MethodCall mc) { \n" +
			"    // Note that \"m5_ok\" is static, so \"mc.f\" will be evaluated (and then ignored). \n" +
			"    // However, the evaluation of \"mc.f\" may fail, since \"mc\" may be null. \n" +
			"    (mc.f).m5_ok(); \n" +
			"  } \n" +
			" \n" +
			"  void new0_ok() { \n" +
			"    MethodCall mc = new MethodCall(); \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result != null; \n" +
			"  MethodCall new1_ok() { \n" +
			"    MethodCall mc = new MethodCall(); \n" +
			"    return mc; \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\result == null; \n" +
			"  MethodCall new2_fail() { \n" +
			"    MethodCall mc = new MethodCall(); \n" +
			"    return mc; \n" +
			"  } \n" +
			" \n" +
			"  /* The following test cases actually test field dereferences, not \n" +
			"   * method calls, but at the time these tests were written, both \n" +
			"   * parts of the checker suffered from a similar problem, so the \n" +
			"   * test cases ended up here. \n" +
			"   */ \n" +
			" \n" +
			"  int x; \n" +
			"  static int g; \n" +
			"   \n" +
			"  int f0_ok() { \n" +
			"    return x; \n" +
			"  } \n" +
			" \n" +
			"  /****  The following method currently crashes the checker \n" +
			"  int f1_ok() { \n" +
			"    return MethodCall.x; \n" +
			"  } \n" +
			"  ****/ \n" +
			" \n" +
			"  int f2_ok() { \n" +
			"    return g; \n" +
			"  } \n" +
			" \n" +
			"  int f3_ok() { \n" +
			"    return MethodCall.g; \n" +
			"  } \n" +
			" \n" +
			"  int f4_ok() { \n" +
			"    MethodCall mc = this; \n" +
			"    int z = g; \n" +
			"    int y = (mc = null).g; \n" +
			"    //@ assert mc == null; \n" +
			"    //@ assert y == z; \n" +
			"    return z + y; \n" +
			"  } \n" +
			" \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_345() {
			this.runNegativeTest(new String[] {
			testsPath + "MethodCall.java", 
			"class SubMethodCall extends MethodCall { \n" +
			" \n" +
			"  // override \n" +
			"  void m4_ok() { \n" +
			"    m4_ok(); \n" +
			"    m5_ok(); \n" +
			"    super.m4_ok(); \n" +
			"    super.m5_ok(); \n" +
			"    this.m4_ok(); \n" +
			"    this.m5_ok(); \n" +
			"    MethodCall.m5_ok(); \n" +
			"    // MethodCall.m4_ok();  // not allowed by Java \n" +
			"  } \n" +
			" \n" +
			"  static void m5sub_ok() { \n" +
			"    m5sub_ok(); \n" +
			"    SubMethodCall.m5sub_ok(); \n" +
			"  } \n" +
			"   \n" +
			"  int f5_ok() { \n" +
			"    return super.x; \n" +
			"  } \n" +
			" \n" +
			"  int f6_ok() { \n" +
			"    return super.g; \n" +
			"  } \n" +
			"   \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_346() {
			this.runNegativeTest(new String[] {
			testsPath + "shift.java", 
			"// test the relative (i.e., op=) form of the \n" +
			"// shift operations (these are the m0,m1,m2 tests, which should pass with \n" +
			"// no warnings. \n" +
			" \n" +
			"// Also test that the long shift operations are not confounded with \n" +
			"// the int shift operations (these are tests p0,p1, and p2, which \n" +
			"// should produce warnings). \n" +
			" \n" +
			"// Also test inclusion of various shift axioms from the universal background \n" +
			"// predicate \n" +
			" \n" +
			"class shift { \n" +
			" \n" +
			"int n; \n" +
			" \n" +
			"//test unsigned right shift \n" +
			"//@modifies n; \n" +
			"//@ensures n == (\\old(n)>>>i); \n" +
			"void m0( int i) { \n" +
			"n>>>=i; \n" +
			"//n= (n>>>i); \n" +
			"} \n" +
			" \n" +
			"//@ensures n == (\\old(n)<<i); \n" +
			"//@modifies n; \n" +
			"void m1(int i) { \n" +
			"n<<=i; \n" +
			"//n= (n<<i); \n" +
			"} \n" +
			" \n" +
			"//@ensures n == (\\old(n)>>i); \n" +
			"//@modifies n; \n" +
			"void m2(int i) { \n" +
			"n>>=i; \n" +
			"//n= (n>>i); \n" +
			"} \n" +
			" \n" +
			"void p0(int k,int m) { \n" +
			"long l= m; \n" +
			"//@ assert (l >> k) == (m >> k); \n" +
			"} \n" +
			" \n" +
			"void p1(int k,int m) { \n" +
			"long l= m; \n" +
			"//@ assert (l >>> k) == (m >>> k); \n" +
			"} \n" +
			" \n" +
			"void p2(int k,int m) { \n" +
			"long l= m; \n" +
			"//@ assert (l << k) == (m << k); \n" +
			"} \n" +
			" \n" +
			"  //@ requires m == l; \n" +
			"  void p3(int k, int m, long l) { \n" +
			"    //@ assert (l << k) == (m << k); \n" +
			"  } \n" +
			" \n" +
			"  //@ requires m == l; \n" +
			"  //@ requires 0 <= k && k < 32; \n" +
			"  void p4(int k, int m, long l) { \n" +
			"    // The following is actually true in Java, but ESC/Java doesn't know it \n" +
			"    //@ assert (l << k) == (m << k); \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures 1 <= \\result; \n" +
			"  int a0(int n) { \n" +
			"    return 1 << n;  // Post violation if n is multiple of 32 minus 1 \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures 1 <= \\result; \n" +
			"  long a1(int n) { \n" +
			"    return 1L << n;  // Post violation if n is multiple of 64 minus 1 \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires (0 <= n && n < 31) || \n" +
			"               (!b && 0 <= n && n < 63) || \n" +
			"	       (7 <= n && n <= 10); */ \n" +
			"  //@ ensures 1 <= \\result; \n" +
			"  long a2(boolean b, int n) { \n" +
			"    if (b) { \n" +
			"      return 1 << n; \n" +
			"    } else { \n" +
			"      return 1L << n; \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_347() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			" \n" +
			"public class C { \n" +
			"    void test0() { \n" +
			"        // skip \n" +
			"    } \n" +
			"    void test1() { \n" +
			"	int x=0; \n" +
			"	//@ assert x == 0; \n" +
			"    } \n" +
			"    void test2() {                  \n" +
			"	int x; \n" +
			"	//@ assert x == 0; // ERROR \n" +
			"    } \n" +
			"    void test3() { \n" +
			"	int x; \n" +
			"	//@ assume x == 0; \n" +
			"    } \n" +
			"    void test4() { \n" +
			"	int x=0; \n" +
			"	//@ assume x == 0; \n" +
			"    } \n" +
			"    void test5() { \n" +
			"	int x=0; \n" +
			"	//@ assert x == 1; // ERROR \n" +
			"    } \n" +
			"    void test6() { \n" +
			"	int x=0; \n" +
			"	//@ assume x == 1; \n" +
			"    } \n" +
			"    void test7() { \n" +
			"	int x=0; \n" +
			"	//@ assume (\\forall int i; i>0); \n" +
			"	//@ assume (\\forall C c; c == c); \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_348() {
			this.runNegativeTest(new String[] {
			testsPath + "Teste.java", 
			"		 \n" +
			"public class Teste {		 \n" +
			"    private static final short BMASK = 0x00FF;		 \n" +
			" 		 \n" +
			"			 \n" +
			"	/**		 \n" +
			"     * Multiply a by b and stores the result in r.		 \n" +
			"     * Requires r.length >= a.length + 1.		 \n" +
			"     *		 \n" +
			"     * @param r the array where the result is to be stored.		 \n" +
			"     * @param a the array containing the value of a.		 \n" +
			"     * @param value the value to multiply for.		 \n" +
			"     * @return r = a * value.		 \n" +
			"     * 		 \n" +
			"     * @throws NullPointerException if either a or r is null.		 \n" +
			"     * @throws ArrayOutOfBoundsException if r.length < a.length + 1.		 \n" +
			"     */		 \n" +
			"    public static void multiply(byte[] r, byte[] a, byte value)		 \n" +		
			"    //@requires r != null & a != null;		 \n" +		
			"    //@requires r.length >= a.length + 1;		 \n" +		
			"    		 \n" +		
			"    {		 \n" +
			"    	short b = (short) (value & BMASK);		 \n" +
			"    	short v=0;		 \n" +
			"    	short idxr = (short)(r.length - 1);		 \n" +
			"    			 \n" +
			"       	for(short idxa = (short) (a.length - 1); idxa>=0; idxa--){			 \n" +
			"    		v += (short) (b * (a[idxa] & BMASK)); 		 \n" +
			"   			r[idxr--] = (byte) v;		 \n" +
			"   			v >>>= 8;		 \n" +
			"			// >>>= works on int type, therefore the short value may remain negative.		 \n" +
			"   			// the following line allows the use of this library on any java environment		 \n" +
			"   			v &= BMASK;		 \n" +
			"   		}		 \n" +
			"   		r[idxr] = (byte) v;		 \n" +
			"   				 \n" +
			"   		//clear the remaining of the r array		 \n" +
			"   		while(idxr!=0)		 \n" +
			"   			r[--idxr] = 0;		 \n" +
			"    }		 \n" +
			"    		 \n" +
			"}		 \n" 
			}, "ERROR");
			}

			public void test_349() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures.java", 
			"class Exsures { \n" +
			"  //@ ensures false \n" +
			"  void m0() throws Throwable { \n" +
			"    throw new Throwable(); \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures false \n" +
			"  void m1() { \n" +
			"    throw new IndexOutOfBoundsException();  // Java is happy with this, but \n" +
			"                                            // ESC/Java issues a complaint \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures false \n" +
			"  void m2() throws IndexOutOfBoundsException { \n" +
			"    throw new IndexOutOfBoundsException();  // both Java and ESC/Java are happy \n" +
			"                                            // with this \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 0 <= x; \n" +
			"  //@ ensures x == 0; \n" +
			"  //@ exsures (Throwable t) 0 < x; \n" +
			"  //@ exsures (SomeException se) 10 < x; \n" +
			"  //@ exsures (SomeException se) x < se.f; \n" +
			"  void m3(int x) throws Throwable { \n" +
			"    switch (x) { \n" +
			"      case 1: \n" +
			"	throw new Throwable(); \n" +
			"      case 12: \n" +
			"	throw new SomeException(x+2); \n" +
			"      case 0: \n" +
			"	break; \n" +
			"      default: \n" +
			"	if (x > 20) { \n" +
			"	  throw new SomeException(x+10); \n" +
			"	} else if (0 <= x) { \n" +
			"	  throw new Throwable(); \n" +
			"	} \n" +
			"	//@ unreachable \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  int ff; \n" +
			"   \n" +
			"  //@ modifies ff; \n" +
			"  //@ exsures (SomeException se) se != p; \n" +
			"  //@ exsures (Throwable t) \\old(ff) < ff; \n" +
			"  void m4(SomeException p) throws SomeException { \n" +
			"    if (p != null) { \n" +
			"      ff++; \n" +
			"      throw new SomeException(2); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires k % m == 0; \n" +
			"  //@ modifies ff; \n" +
			"  //@ ensures k == 0; \n" +
			"  //@ ensures ff == 5; \n" +
			"  //@ exsures (SomeException ss) m != 2; \n" +
			"  void m5(int k, int m) throws SomeException { \n" +
			"    int w = 2; \n" +
			"    try { \n" +
			"      SomeException se = new SomeException(k, m); \n" +
			"      w = 3; \n" +
			"    } catch (SomeException s) { \n" +
			"      //@ assert m != 2; \n" +
			"      throw s; \n" +
			"    } catch (Throwable t) { \n" +
			"      //@ assert k == 0; \n" +
			"      return; \n" +
			"    } finally { \n" +
			"      ff = 5; \n" +
			"      // return if a \"Throwable\" was caught; otherwise, fall through \n" +
			"    } \n" +
			"    //@ assert w == 3; \n" +
			"    do { \n" +
			"      // skip \n" +
			"    } while (k != 0); \n" +
			"  } \n" +
			" \n" +
			"  //@ modifies ff; \n" +
			"  //@ ensures ff == 0 \n" +
			"  //@ exsures (SomeException se) se.f <= \\old(ff); \n" +
			"  void m6() throws SomeException { \n" +
			"    if (ff == 0) { \n" +
			"      // skip \n" +
			"    } else if (10 < ff) { \n" +
			"      ff = -2; \n" +
			"      throw new SomeException(2); \n" +
			"    } else { \n" +
			"      // the following \"throw\" may fail to satisfy the exceptional \n" +
			"      // postcondition \n" +
			"      throw new SomeException(4); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ modifies ff; \n" +
			"  //@ ensures ff == 0 \n" +
			"  //@ exsures (SomeException se) se.f <= \\old(ff); \n" +
			"  void m7() throws Throwable { \n" +
			"    if (ff == 0) { \n" +
			"      // skip \n" +
			"    } else if (10 < ff) { \n" +
			"      ff = -2; \n" +
			"      throw new SomeException(2); \n" +
			"    } else { \n" +
			"      ff = 12; \n" +
			"      throw new Throwable(); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  Exsures() throws Throwable { \n" +
			"  } \n" +
			" \n" +
			"  //@ exsures (Throwable t) super0 == super1; \n" +
			"  void m8(int super0, int super1) throws Throwable { \n" +
			"    if (super0 == super1) { \n" +
			"      throw new Throwable(); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ exsures (Throwable t) super0 == super1; \n" +
			"  void m9(int super0, int super1) throws Throwable { \n" +
			"    m8(super0, super1); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_350() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures.java", 
			"class SomeException extends Throwable { \n" +
			"  int f; \n" +
			"   \n" +
			"  //@ ensures f == y; \n" +
			"  SomeException(int y) { \n" +
			"    f = y; \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures f == a + b; \n" +
			"  //@ exsures (Throwable t) a == 0 || t instanceof SomeException; \n" +
			"  //@ exsures (SomeException se) a % 2 != 0; \n" +
			"  SomeException(int a, int b) throws Throwable { \n" +
			"    if (a % 2 == 0) { \n" +
			"      f = a + b; \n" +
			"    } else { \n" +
			"      throw this;  // this seems like a bad idea, but ESC/Java won't catch it \n" +
			"    } \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_351() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures.java", 
			"class AlsoExsures extends Exsures { \n" +
			"  int gg; \n" +
			"  //@ also \n" +
			"  //@ modifies gg; \n" +
			"  //@ ensures ff < 10 && gg == 4; \n" +
			"  //@ exsures (SomeException se) gg == se.f; \n" +
			"  void m6() throws SomeException { \n" +
			"    gg = 3; \n" +
			"    try { \n" +
			"      super.m6(); \n" +
			"    } catch (SomeException se) { \n" +
			"      gg = se.f - 1; \n" +
			"      try { \n" +
			"	throw se; \n" +
			"      } finally { \n" +
			"	gg++; \n" +
			"      } \n" +
			"    } \n" +
			"    //@ assert gg == 3; \n" +
			"    ++gg; \n" +
			"  } \n" +
			" \n" +
			"  // The following constructor may fail to establish its exceptional \n" 
			}, "ERROR");
			}

			public void test_352() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures.java", 
			"  // postcondition, because the implicit call to the superclass constructor \n" +
			"  // may throw a \"SomeException\". \n" +
			"  //@ requires ae != null; \n" +
			"  //@ exsures (SomeException se) ae.gg == 17 && ae.gg == se.f; \n" +
			"  AlsoExsures(AlsoExsures ae) throws Throwable { \n" +
			"    if (ae.gg == 17) { \n" +
			"      throw new SomeException(ae.gg); \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  //@ also \n" +
			"  //@ exsures (Throwable t) 0 < sub0; \n" +
			"  //@ exsures (Throwable t) sub1 < 10; \n" +
			"  void m8(int sub0, int sub1) throws Throwable { \n" +
			"    if (0 < sub0 && sub1 < 10 && sub0 == sub1) { \n" +
			"      throw new Throwable(); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  // The following method may fail to establish the \"exsures\" clause declared \n" +
			"  // in the superclass. \n" +
			"  //@ also \n" +
			"  //@ exsures (Throwable t) 0 < sub0; \n" +
			"  //@ exsures (Throwable t) sub1 < 10; \n" +
			"  void m9(int sub0, int sub1) throws Throwable { \n" +
			"    if (0 < sub0 && sub1 < 10) { \n" +
			"      throw new Throwable(); \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_353() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures2.java", 
			"class Exsures2 { \n" +
			"  //@ ensures false \n" +
			"  void m0() throws Throwable { \n" +
			"    throw new Throwable(); \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures false \n" +
			"  void m1() { \n" +
			"    throw new IndexOutOfBoundsException();  // Java is happy with this, but \n" +
			"                                            // ESC/Java issues a complaint \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures false \n" +
			"  void m2() throws IndexOutOfBoundsException { \n" +
			"    throw new IndexOutOfBoundsException();  // both Java and ESC/Java are happy \n" +
			"                                            // with this \n" +
			"  } \n" +
			" \n" +
			"  //@ requires 0 <= x; \n" +
			"  //@ ensures x == 0; \n" +
			"  //@ exsures (Throwable ) 0 < x; \n" +
			"  //@ exsures (SomeException ) 10 < x; \n" +
			"  //@ exsures (SomeException se) x < se.f; \n" +
			"  void m3(int x) throws Throwable { \n" +
			"    switch (x) { \n" +
			"      case 1: \n" +
			"	throw new Throwable(); \n" +
			"      case 12: \n" +
			"	throw new SomeException(x+2); \n" +
			"      case 0: \n" +
			"	break; \n" +
			"      default: \n" +
			"	if (x > 20) { \n" +
			"	  throw new SomeException(x+10); \n" +
			"	} else if (0 <= x) { \n" +
			"	  throw new Throwable(); \n" +
			"	} \n" +
			"	//@ unreachable \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  int ff; \n" +
			"   \n" +
			"  //@ modifies ff; \n" +
			"  //@ exsures (SomeException se) se != p; \n" +
			"  //@ exsures (Throwable) \\old(ff) < ff; \n" +
			"  void m4(SomeException p) throws SomeException { \n" +
			"    if (p != null) { \n" +
			"      ff++; \n" +
			"      throw new SomeException(2); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires k % m == 0; \n" +
			"  //@ modifies ff; \n" +
			"  //@ ensures k == 0; \n" +
			"  //@ ensures ff == 5; \n" +
			"  //@ exsures (SomeException ) m != 2; \n" +
			"  void m5(int k, int m) throws SomeException { \n" +
			"    int w = 2; \n" +
			"    try { \n" +
			"      SomeException se = new SomeException(k, m); \n" +
			"      w = 3; \n" +
			"    } catch (SomeException s) { \n" +
			"      //@ assert m != 2; \n" +
			"      throw s; \n" +
			"    } catch (Throwable t) { \n" +
			"      //@ assert k == 0; \n" +
			"      return; \n" +
			"    } finally { \n" +
			"      ff = 5; \n" +
			"      // return if a \"Throwable\" was caught; otherwise, fall through \n" +
			"    } \n" +
			"    //@ assert w == 3; \n" +
			"    do { \n" +
			"      // skip \n" +
			"    } while (k != 0); \n" +
			"  } \n" +
			" \n" +
			"  //@ modifies ff; \n" +
			"  //@ ensures ff == 0 \n" +
			"  //@ exsures (SomeException se) se.f <= \\old(ff); \n" +
			"  void m6() throws SomeException { \n" +
			"    if (ff == 0) { \n" +
			"      // skip \n" +
			"    } else if (10 < ff) { \n" +
			"      ff = -2; \n" +
			"      throw new SomeException(2); \n" +
			"    } else { \n" +
			"      // the following \"throw\" may fail to satisfy the exceptional \n" +
			"      // postcondition \n" +
			"      throw new SomeException(4); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ modifies ff; \n" +
			"  //@ ensures ff == 0 \n" +
			"  //@ exsures (SomeException se) se.f <= \\old(ff); \n" +
			"  void m7() throws Throwable { \n" +
			"    if (ff == 0) { \n" +
			"      // skip \n" +
			"    } else if (10 < ff) { \n" +
			"      ff = -2; \n" +
			"      throw new SomeException(2); \n" +
			"    } else { \n" +
			"      ff = 12; \n" +
			"      throw new Throwable(); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  Exsures2() throws Throwable { \n" +
			"  } \n" +
			" \n" +
			"  //@ exsures (Throwable ) super0 == super1; \n" +
			"  void m8(int super0, int super1) throws Throwable { \n" +
			"    if (super0 == super1) { \n" +
			"      throw new Throwable(); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ exsures (Throwable ) super0 == super1; \n" +
			"  void m9(int super0, int super1) throws Throwable { \n" +
			"    m8(super0, super1); \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_354() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures2.java", 
			"class SomeException2 extends Throwable { \n" +
			"  int f; \n" +
			"   \n" +
			"  //@ ensures f == y; \n" +
			"  SomeException2(int y) { \n" +
			"    f = y; \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures f == a + b; \n" +
			"  //@ exsures (Throwable t) a == 0 || t instanceof SomeException2; \n" +
			"  //@ exsures (SomeException2 ) a % 2 != 0; \n" +
			"  SomeException2(int a, int b) throws Throwable { \n" +
			"    if (a % 2 == 0) { \n" +
			"      f = a + b; \n" +
			"    } else { \n" +
			"      throw this;  // this seems like a bad idea, but ESC/Java won't catch it \n" +
			"    } \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_355() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures2.java", 
			"class AlsoExsures2 extends Exsures2 { \n" +
			"  int gg; \n" +
			"  //@ also \n" +
			"  //@ modifies gg; \n" +
			"  //@ ensures ff < 10 && gg == 4; \n" +
			"  //@ exsures (SomeException se) gg == se.f; \n" +
			"  void m6() throws SomeException { \n" +
			"    gg = 3; \n" +
			"    try { \n" +
			"      super.m6(); \n" +
			"    } catch (SomeException se) { \n" +
			"      gg = se.f - 1; \n" +
			"      try { \n" +
			"	throw se; \n" +
			"      } finally { \n" +
			"	gg++; \n" +
			"      } \n" +
			"    } \n" +
			"    //@ assert gg == 3; \n" +
			"    ++gg; \n" +
			"  } \n" +
			" \n" +
			"  // The following constructor may fail to establish its exceptional \n" 
			}, "ERROR");
			}

			public void test_356() {
			this.runNegativeTest(new String[] {
			testsPath + "Exsures2.java", 
			"  // postcondition, because the implicit call to the superclass constructor \n" +
			"  // may throw a \"SomeException\". \n" +
			"  //@ requires ae != null; \n" +
			"  //@ exsures (SomeException se) ae.gg == 17 && ae.gg == se.f; \n" +
			"  AlsoExsures2(AlsoExsures2 ae) throws Throwable { \n" +
			"    if (ae.gg == 17) { \n" +
			"      throw new SomeException(ae.gg); \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  //@ also \n" +
			"  //@ exsures (Throwable ) 0 < sub0; \n" +
			"  //@ exsures (Throwable ) sub1 < 10; \n" +
			"  void m8(int sub0, int sub1) throws Throwable { \n" +
			"    if (0 < sub0 && sub1 < 10 && sub0 == sub1) { \n" +
			"      throw new Throwable(); \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  // The following method may fail to establish the \"exsures\" clause declared \n" +
			"  // in the superclass. \n" +
			"  //@ also \n" +
			"  //@ exsures (Throwable ) 0 < sub0; \n" +
			"  //@ exsures (Throwable ) sub1 < 10; \n" +
			"  void m9(int sub0, int sub1) throws Throwable { \n" +
			"    if (0 < sub0 && sub1 < 10) { \n" +
			"      throw new Throwable(); \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_357() {
			this.runNegativeTest(new String[] {
			testsPath + "ge0.java", 
			"class C { \n" +
			" \n" +
			"    void foo() {	 \n" +
			"	for(int i = 0; i < 10; i++) { \n" +
			"	    //@ assert i >= 0; \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    void goo1() { \n" +
			"	int k = 1; \n" +
			" \n" +
			"	for(int i = 0; i < 10; i++) { \n" +
			"	    k++; \n" +
			"	}	 \n" +
			"	//@ assert k >= 1; \n" +
			"    } \n" +
			" \n" +
			"    void goo2() { \n" +
			"	int k = 1; \n" +
			" \n" +
			"	for(int i = 0; i < 10; i++) { \n" +
			"	    k--; \n" +
			"	}	 \n" +
			"	//@ assert k <= 1; \n" +
			"    } \n" +
			" \n" +
			"    Object [] ta = new Object[10]; \n" +
			"    //@ invariant ta != null \n" +
			"     \n" +
			"    void loo() { \n" +
			"	Object[] a = ta; \n" +
			"	 \n" +
			"	for (int i = 0; i < a.length; i++) \n" +
			"	    a[i] = null; \n" +
			"	//@ assert (\\forall int j; 0 <= j && j < a.length ==> a[j] == null); \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_358() {
			this.runNegativeTest(new String[] {
			testsPath + "neqnull.java", 
			"class C { \n" +
			" \n" +
			"    void foo() { \n" +
			" \n" +
			"	Object a = new Object(); \n" +
			"	for(int i = 0; i < 10; i++) { \n" +
			"	    //@ assert i >= 0; \n" +
			"	    a = a; \n" +
			"	    //@ assert a != null; \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_359() {
			this.runNegativeTest(new String[] {
			testsPath + "test-old.java", 
			"class c { \n" +
			"    static int x,y; \n" +
			"     \n" +
			"    //@ ensures x+y > \\old(x+y); \n" +
			"    //@ modifies y; \n" +
			"    void m() { \n" +
			"	x++; \n" +
			"    } \n" +
			" \n" +
			"    void mi() { \n" +
			"	y = 0; \n" +
			"	//@ loop_invariant x+y == \\old(x); \n" +
			"	for(;;) { \n" +
			"	    x++; \n" +
			"	    y--; \n" +
			"	} \n" +
			"    } \n" +
			"    void mp() { \n" +
			"	y = 0; \n" +
			"	int oldx = x; \n" +
			"	//@ loop_predicate x+y == \\old(x); \n" +
			"	for(;;) { \n" +
			"	    x++; \n" +
			"	    y--; \n" +
			"	    //@ assert x+y == oldx; \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_360() {
			this.runNegativeTest(new String[] {
			testsPath + "preciseTargets.java", 
			"class C { \n" +
			" \n" +
			"    int i; \n" +
			" \n" +
			"    void m(C c, int[] j, int[] k) { \n" +
			"	 \n" +
			"	//@ assume this != c; \n" +
			"	//@ assume null != c; \n" +
			"	//@ assume i >= 0; \n" +
			"	//@ assume j[0] >= 0; \n" +
			"	//@ assume j.length > 4; \n" +
			"	//@ assume j != null; \n" +
			"	//@ assume j != k; \n" +
			"	//@ assume k[1] >= 0; \n" +
			"	//@ assume k.length > 4; \n" +
			"	//@ assume k != null \n" +
			" \n" +
			"	for(;;) { \n" +
			"	    c.i --; \n" +
			"	    //@ assert i >= 0; \n" +
			"	    j[1]--; \n" +
			"	    //@ assert j[0] >= 0; \n" +
			"	    //@ assert k[1] >= 0; \n" +
			"	    n(c,j); \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    //@ modifies c.i, j[2]; \n" +
			"    void n(C c, int[] j) { \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_361() {
			this.runNegativeTest(new String[] {
			testsPath + "B.java", 
			"class B { \n" +
			"    // test pred abs \n" +
			" \n" +
			"    static boolean t; \n" +
			"    static boolean t() { \n" +
			"	return true; \n" +
			"    } \n" +
			" \n" +
			"    static Object a,b; \n" +
			" \n" +
			"    // test loop context \n" +
			"    static void b1() { \n" +
			"	//@ assume a != null; \n" +
			"	//@ loop_predicate a != null; \n" +
			"	while( t() ) { \n" +
			"	    a = a; \n" +
			"	    a.toString(); \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    // test preconditions \n" +
			"    //@ requires a != null; \n" +
			"    static void b2() { \n" +
			"	//@ loop_predicate a != null; \n" +
			"	while( t() ) { \n" +
			"	    a = a; \n" +
			"	    a.toString(); \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    // test loop guard \n" +
			"    static void b3() { \n" +
			"	//@ assume a != null; \n" +
			"	//@ loop_predicate a != null; \n" +
			"	while( t() && b != null ) { \n" +
			"	    a = b; b=b; \n" +
			"	} \n" +
			"	a.toString(); \n" +
			"    } \n" +
			" \n" +
			"    // test invariants \n" +
			"    static void b4() { \n" +
			"	//@ assume a != null; \n" +
			"	//@ assume b != null; \n" +
			"	//@ loop_predicate a != null; \n" +
			"	//@ loop_invariant b != null; \n" +
			"	while( t() ) { \n" +
			"	    a = b; b=b; \n" +
			"	} \n" +
			"	a.toString(); \n" +
			"    } \n" +
			" \n" +
			"    // test nested loops \n" +
			"    static void b5() { \n" +
			"	//@ assume a != null; \n" +
			"	//@ loop_predicate a != null; \n" +
			"	while( t ) { \n" +
			"	    a = a; \n" +
			"	    //a.toString(); \n" +
			"	    //@ loop_predicate a != null; \n" +
			"	    while( t ) { \n" +
			"		a = a; \n" +
			"		//a.toString(); \n" +
			"	    } \n" +
			"	} \n" +
			"	a.toString(); \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_362() {
			this.runNegativeTest(new String[] {
			testsPath + "B.java", 
			"class E { \n" +
			" \n" +
			"    static int i; \n" +
			"    //@ invariant i >= 0; \n" +
			" \n" +
			"    static void foo() { \n" +
			" \n" +
			"	//@ loop_predicate i >= 0 \n" +
			" \n" +
			"	for(int j = 0; j < 10; j++) { \n" +
			"	    i++; \n" +
			"	} \n" +
			"	//@ assert i >= 0; \n" +
			" \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_363() {
			this.runNegativeTest(new String[] {
			testsPath + "E.java", 
			"class E { \n" +
			" \n" +
			"    static int i; \n" +
			"    //@ invariant i >= 0; \n" +
			" \n" +
			"    static void foo() { \n" +
			" \n" +
			"	//@ loop_predicate i >= 0; \n" +
			" \n" +
			"	for(int j = 0; j < 10; j++) { \n" +
			"	    i++; \n" +
			"	} \n" +
			"	//@ assert i >= 0; \n" +
			" \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_364() {
			this.runNegativeTest(new String[] {
			testsPath + "F.java", 
			"class F { \n" +
			"    /*@ non_null */ static int a[]; \n" +
			"    void m() { \n" +
			"        int i; \n" +
			"	//@ skolem_constant int c;  \n" +
			"	// skolem_constant int l;  \n" +
			"	// skolem_constant java.lang.Object b[];  \n" +
			"         \n" +
			"	//@ loop_predicate i >= 0; \n" +
			"	//@ loop_predicate c >= 0, c < i; \n" +
			"	//@ loop_predicate a[c] == 0; \n" +
			"	for(i = 0; i < a.length; i++) { \n" +
			"	    a[i] = 0; \n" +
			"	    //@ assert (\\forall int j; 0 <= j && j <= i ==> a[j] == 0 ); \n" +
			"	} \n" +
			"	//@ assert (\\forall int j; 0 <= j && j < a.length ==> a[j] == 0 ); \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_365() {
			this.runNegativeTest(new String[] {
			testsPath + "D.java", 
			"class D { \n" +
			"    /*@ non_null */ static int [][] a;  \n" +
			"    //@ invariant \\nonnullelements(a); \n" +
			"    D(){} //@ nowarn \n" +
			" \n" +
			"    void foo5 () {	 \n" +
			"	int[] b = a[0]; \n" +
			"	a[0][0] = 0; \n" +
			"	//@ assert b == a[0]; \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_366() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C0 { \n" +
			" \n" +
			"    C0() { } //@ nowarn \n" +
			" \n" +
			"    /*@ non_null */ static int [] a;  \n" +
			"    static int c; \n" +
			" \n" +
			"    void foo000 () {	 \n" +
			"	// Use these constants to check that we get info \n" +
			"	// from loop context \n" +
			"	int zero1 = 0, zero2 = 0; \n" +
			" \n" +
			"	//@ assume 0<=c \n" +
			"	/*@ loop_predicate c < i, a[c] == 0, i < 0 */ \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			"	    a[i] = zero1; \n" +
			"	} \n" +
			"	 \n" +
			"	/*@ assert 0 <= c && c < a.length ==> a[c] == zero2 */ \n" +
			"    } \n" +
			"    void foo00 () {	 \n" +
			"	// Use these constants to check that we get info \n" +
			"	// from loop context \n" +
			"	int zero1 = 0, zero2 = 0; \n" +
			" \n" +
			"	/*@ loop_predicate 0 <= c, c < i, a[c] == 0, i < 0 */ \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			"	    a[i] = zero1; \n" +
			"	} \n" +
			"	 \n" +
			"	/*@ assert 0 <= c && c < a.length ==> a[c] == zero2 */ \n" +
			"    } \n" +
			"} \n" +
			" \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_367() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C1 {  // Tests 2d arrays \n" +
			" \n" +
			"    C1() { } //@ nowarn \n" +
			" \n" +
			"    /*@ non_null */ static int [][] a;  \n" +
			"    //@ invariant \\nonnullelements(a); \n" +
			"    static int c,d; \n" +
			" \n" +
			"    void foo10 () {	 \n" +
			"	//@ assume a.length >0 \n" +
			"	//@ assume a[0].length >0 \n" +
			" \n" +
			"	int[] b = a[0]; \n" +
			"	a[0][0] = 0; \n" +
			"	//@ assert b == a[0]; \n" +
			"    } \n" +
			" \n" +
			"    void foo11 () {	 \n" +
			"	//@ assume a.length >0 \n" +
			"	//@ assume a[0].length >0 \n" +
			" \n" +
			"	//@ loop_invariant a[0] == \\old(a[0]); \n" +
			"	while(true) { \n" +
			"	    a[0][0] = 0; \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    void foo12 () {	 \n" +
			"	//@ assume 0 <= c && c < a.length \n" +
			" \n" +
			"	//@ loop_invariant j >= 0; \n" +
			"	//@ loop_invariant a[c] == \\old(a[c]); \n" +
			"	//@ loop_invariant a[0] == \\old(a[0]); \n" +
			"	//@ loop_invariant \\nonnullelements(a); \n" +
			" \n" +
			"	for (int j = 0; j < a[c].length; j++) { \n" +
			"	    a[c][j] = 0; \n" +
			"	} \n" +
			"	 \n" +
			"    } \n" +
			" \n" +
			"    void foo13 () {	 \n" +
			"	//@ assume 0 <= c && c < a.length \n" +
			" \n" +
			"	// loop_invariant a[c] == \\old(a[c]); \n" +
			"	// loop_invariant a[0] == \\old(a[0]); \n" +
			"	// loop_invariant a[c] != a ; \n" +
			" \n" +
			"	//@ loop_invariant 0 <= d && d < j ==> a[c][d] == 0  \n" +
			"	//@ loop_invariant j >= 0; \n" +
			"	//@ loop_invariant \\nonnullelements(a); \n" +
			"	for (int j = 0; j < a[c].length; j++) { \n" +
			"	    //@ assert 0 <= d && d < j ==> a[c][d] == 0  \n" +
			"	    //@ assert j >= 0; \n" +
			"	    //@ assert \\nonnullelements(a); \n" +
			"	    a[c][j] = 0; \n" +
			"	    //@ assert \\nonnullelements(a); \n" +
			"	} \n" +
			"	 \n" +
			"	/*@ assert 0 <= c && c < a.length && 0 <= d && d < a[c].length  \n" +
			"	  ==> a[c][d] == 0 */ \n" +
			"    } \n" +
			" \n" +
			"    void foo14 () {	 \n" +
			" \n" +
			"	// loop_invariant \\nonnullelements(a); \n" +
			"	//@ loop_predicate \\nonnullelements(a); \n" +
			"	while(true) { \n" +
			"	    //@ assert \\nonnullelements(a); \n" +
			"	    a[0][0] = 0;  //@ nowarn IndexTooBig \n" +
			"	    //@ assert \\nonnullelements(a); \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    void foo15 () {	 \n" +
			" \n" +
			"	//@ assert \\nonnullelements(a); \n" +
			" \n" +
			"	// loop_invariant \\nonnullelements(a); \n" +
			" \n" +
			"	//@ loop_predicate \\nonnullelements(a); \n" +
			"	while(true) { \n" +
			"	    //@ assert \\nonnullelements(a); \n" +
			"	    a[0][0] = 0;  //@ nowarn IndexTooBig \n" +
			"	    //@ assert \\nonnullelements(a); \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			"    void foo16 () {	 \n" +
			"	//@ assume 0 <= c && c < a.length \n" +
			" \n" +
			"	// loop_invariant 0 <= d && d < j ==> a[c][d] == 0  \n" +
			"	// loop_invariant \\nonnullelements(a); \n" +
			" \n" +
			"	//@ loop_predicate 0 <= d, d < j, a[c][d] == 0  \n" +
			"	//@ loop_predicate j >= 0; \n" +
			"	//@ loop_predicate \\nonnullelements(a); \n" +
			"	for (int j = 0; j < a[c].length; j++) { \n" +
			"	    // assert 0 <= d && d < j ==> a[c][d] == 0  \n" +
			"	    // assert j >= 0; \n" +
			"	    // assert \\nonnullelements(a); \n" +
			"	    a[c][j] = 0; \n" +
			"	    // assert \\nonnullelements(a); \n" +
			"	} \n" +
			"	 \n" +
			"	/*@ assert 0 <= c && c < a.length && 0 <= d && d < a[c].length  \n" +
			"	  ==> a[c][d] == 0 */ \n" +
			"    } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_368() {
			this.runNegativeTest(new String[] {
			testsPath + "C2.java", 
			" \n" +
			"class C2 { \n" +
			" \n" +
			"    C2() { } //@ nowarn \n" +
			" \n" +
			"    /*@ non_null */ static int [][] a;  \n" +
			"    //@ invariant \\nonnullelements(a); \n" +
			"    static int c,d; \n" +
			" \n" +
			"    void foo20 () {	 \n" +
			"	// loop_invariant \\nonnullelements(a); \n" +
			"	//@ loop_predicate \\nonnullelements(a); \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			" \n" +
			"	    //@ assert \\nonnullelements(a); \n" +
			" \n" +
			"	    // loop_invariant \\nonnullelements(a); \n" +
			"	    //@ loop_predicate \\nonnullelements(a); \n" +
			"	    for (int j = 0; j < a[i].length; j++) { //@ nowarn IndexNegative, IndexTooBig \n" +
			"		//@ assert \\nonnullelements(a); \n" +
			"		a[i][j] = 0; //@ nowarn IndexNegative, IndexTooBig \n" +
			"		//@ assert \\nonnullelements(a); \n" +
			"	    } \n" +
			"	} \n" +
			"    } \n" +
			" \n" +
			" \n" +
			"    void foo21 () {	 \n" +
			"	//@ assume 0 <= c && 0 <= d; \n" +
			" \n" +
			"	// need this \n" +
			"	// loop_invariant c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			" \n" +
			"	//@ loop_invariant i >= 0; \n" +
			"	//@ loop_invariant \\nonnullelements(a); \n" +
			" \n" +
			"	//@ loop_predicate c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	// loop_predicate i >= 0; \n" +
			"	// loop_predicate \\nonnullelements(a); \n" +
			" \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			"	     \n" +
			"	    // assert c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			" \n" +
			"	    // assert \\nonnullelements(a); \n" +
			" \n" +
			"	    int j; \n" +
			" \n" +
			"	    //@ loop_invariant c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	    //@ loop_invariant d < j ==> a[i][d] == 0; \n" +
			"	    //@ loop_invariant \\nonnullelements(a); \n" +
			"	    //@ loop_invariant j >= 0; \n" +
			" \n" +
			"	    // loop_predicate ((c < i && d < a[c].length) ==> a[c][d] == 0); \n" +
			"	    // loop_predicate d < j ==> a[i][d] == 0; \n" +
			"	    // loop_predicate c < i, d < a[c].length, a[c][d] == 0; \n" +
			"	    // loop_predicate d < j, a[i][d] == 0; \n" +
			"	    // loop_predicate \\nonnullelements(a); \n" +
			"	    // loop_predicate j >= 0; \n" +
			" \n" +
			"	    for (j = 0; j < a[i].length; j++) { \n" +
			"		// assert ((c < i && d < a[c].length) ==> a[c][d] == 0); \n" +
			"		// assert d < j ==> a[i][d] == 0; \n" +
			"		// assert \\nonnullelements(a); \n" +
			"		a[i][j] = 0; \n" +
			"		// assert \\nonnullelements(a); \n" +
			"	    } \n" +
			"	    // assert c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	    // assert d < j ==> a[i][d] == 0; \n" +
			"	    // assert j >= a[i].length; \n" +
			"	    //@ assert !(j < a[i].length); \n" +
			"	    // assert d < a[i].length ==> a[i][d] == 0; \n" +
			"	    //@ assert c < i+1 && d < a[c].length ==> a[c][d] == 0; \n" +
			"	} \n" +
			"	 \n" +
			"	/*@ assert 0 <= c && c < a.length && 0 <= d && d < a[c].length \n" +
			"                   ==> a[c][d] == 0; */ \n" +
			"    } \n" +
			" \n" +
			"    void foo22 () {	 \n" +
			"	//@ assume 0 <= c && 0 <= d; \n" +
			" \n" +
			"	/* loop_predicate 0 <= c, 0 <= d, c < i, c = i,  \n" +
			"	  d < j, d < a[c].length, a[c][d] == 0,  \n" +
			"	  i >= 0; \n" +
			"	*/ \n" +
			" \n" +
			"	// loop_invariant \\nonnullelements(a); \n" +
			"	// loop_invariant c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			" \n" +
			"	// loop_predicate c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			" \n" +
			"	//@ loop_predicate c < i, d < a[c].length, a[c][d] == 0; \n" +
			"	//@ loop_predicate i >= 0; \n" +
			"	//@ loop_predicate \\nonnullelements(a); \n" +
			" \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			" \n" +
			"	    //@ assert c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	    //@ assert \\nonnullelements(a); \n" +
			" \n" +
			"	    // loop_invariant c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	    // loop_invariant d < j ==> a[i][d] == 0; \n" +
			" \n" +
			"	    // loop_predicate c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	    // loop_predicate d < j ==> a[i][d] == 0; \n" +
			" \n" +
			"	    //@ loop_predicate c < i, d < a[c].length, a[c][d] == 0; \n" +
			"	    //@ loop_predicate d < j, a[i][d] == 0; \n" +
			"	    //@ loop_predicate j >= 0; \n" +
			"	    //@ loop_predicate \\nonnullelements(a); \n" +
			" \n" +
			"	    for (int j = 0; j < a[i].length; j++) { \n" +
			"		//@ assert d < j ==> a[i][d] == 0; \n" +
			"		//@ assert \\nonnullelements(a); \n" +
			"		a[i][j] = 0; \n" +
			"		//@ assert \\nonnullelements(a); \n" +
			"	    } \n" +
			"	    //@ assert c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	} \n" +
			"	 \n" +
			"	/*@ assert 0 <= c && c < a.length && 0 <= d && d < a[c].length  \n" +
			"                   ==> a[c][d] == 0;*/ \n" +
			"    } \n" +
			" \n" +
			"    void foo23 () {	 \n" +
			"	// assume 0 <= c && 0 <= d; \n" +
			" \n" +
			"	// loop_invariant \\nonnullelements(a); \n" +
			"	// loop_invariant c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			" \n" +
			"	// loop_predicate c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			" \n" +
			"	//@ loop_predicate c < i, d < a[c].length, a[c][d] == 0; \n" +
			"	//@ loop_predicate i >= 0; \n" +
			"	//@ loop_predicate \\nonnullelements(a); \n" +
			"	//@ loop_predicate 0 <= c, 0 <= d; \n" +
			" \n" +
			"	for (int i = 0; i < a.length; i++) { \n" +
			" \n" +
			"	    //@ assert (0 <= c && 0 <= d && c < i && d < a[c].length) ==> a[c][d] == 0; \n" +
			"	    //@ assert \\nonnullelements(a); \n" +
			" \n" +
			"	    // loop_invariant c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	    // loop_invariant d < j ==> a[i][d] == 0; \n" +
			" \n" +
			"	    // loop_predicate c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	    // loop_predicate d < j ==> a[i][d] == 0; \n" +
			" \n" +
			"	    //@ loop_predicate c < i, d < a[c].length, a[c][d] == 0; \n" +
			"	    //@ loop_predicate d < j, a[i][d] == 0; \n" +
			"	    //@ loop_predicate j >= 0; \n" +
			"	    //@ loop_predicate \\nonnullelements(a); \n" +
			"	    //@ loop_predicate 0 <= c, 0 <= d; \n" +
			" \n" +
			"	    for (int j = 0; j < a[i].length; j++) { \n" +
			"		//@ assert 0 <= d && d < j ==> a[i][d] == 0; \n" +
			"		//@ assert \\nonnullelements(a); \n" +
			"		a[i][j] = 0; \n" +
			"		//@ assert \\nonnullelements(a); \n" +
			"	    } \n" +
			"	    //@ assert 0 <= c && 0 <= d && c < i && d < a[c].length ==> a[c][d] == 0; \n" +
			"	} \n" +
			"	 \n" +
			"	/*@ assert 0 <= c && c < a.length && 0 <= d && d < a[c].length  \n" +
			"                   ==> a[c][d] == 0; */ \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_369() {
			this.runNegativeTest(new String[] {
			testsPath + "elems.java", 
			"class C { \n" +
			" \n" +
			"    int[] p; \n" +
			" \n" +
			"    void foo() { \n" +
			"	p = new int[10]; \n" +
			" \n" +
			"	for(int i = 0; i < 10; i++) { \n" +
			"	    p[i]++; \n" +
			"	} \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_370() {
			this.runNegativeTest(new String[] {
			testsPath + "SmallFresh.java", 
			"class SmallFresh { \n" +
			"  int[] a; \n" +
			"  Object f; \n" +
			" \n" +
			"  //@ ensures !\\fresh(o) \n" +
			"  void p0(Object o) { \n" +
			"  } \n" +
			"   \n" +
			"  //@ ensures !\\fresh(f) \n" +
			"  void p1() { \n" +
			"  } \n" +
			"   \n" +
			"  //@ modifies f \n" +
			"  //@ ensures \\fresh(\\old(f)) != \\fresh(f) \n" +
			"  void m0() { \n" +
			"    f = new Object(); \n" +
			"  } \n" +
			"   \n" +
			"  //@ modifies a \n" +
			"  //@ ensures \\fresh(\\old(a)) != \\fresh(a) \n" +
			"  void m1() { \n" +
			"    a = new int[10]; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_371() {
			this.runNegativeTest(new String[] {
			testsPath + "Fresh.java", 
			"class Fresh { \n" +
			"  int[] a; \n" +
			"  Object f; \n" +
			"   \n" +
			"  //@ ensures \\fresh(this) \n" +
			"  Fresh() { \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\fresh(this) \n" +
			"  //@ ensures \\fresh(f) \n" +
			"  /*@ ensures \\fresh(a) */  // fails to establish this one \n" +
			"  Fresh(int[] p) { \n" +
			"    f = new Object(); \n" +
			"    a = p; \n" +
			"  }  // fails to establish postcondition \n" +
			" \n" +
			"  //@ requires 0 <= n; \n" +
			"  //@ ensures \\fresh(this) \n" +
			"  //@ ensures \\fresh(a) \n" +
			"  Fresh(int n) { \n" +
			"    a = new int[n]; \n" +
			"  } \n" +
			" \n" +
			"  //@ modifies a \n" +
			"  /*@ ensures \\fresh(\\old(a)) */  // impossible to establish \n" +
			"  void m0() { \n" +
			"    a = new int[10]; \n" +
			"  }  // fails to establish impossible postcondition \n" +
			"   \n" +
			"  //@ modifies a \n" +
			"  //@ ensures \\fresh(\\old(a)) != \\fresh(a) \n" +
			"  void m1() { \n" +
			"    a = new int[10]; \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\fresh(\\result) \n" +
			"  Object m2() { \n" +
			"    return null; \n" +
			"  }  // fails to establish postcondition \n" +
			" \n" +
			"  //@ ensures \\fresh(\\result) \n" +
			"  Object m3() { \n" +
			"    return a; \n" +
			"  }  // fails to establish postcondition \n" +
			" \n" +
			"  //@ ensures \\fresh(\\result) \n" +
			"  Object m4() { \n" +
			"    return new int[12]; \n" +
			"  } \n" +
			" \n" +
			"  //@ ensures \\fresh(\\result) \n" +
			"  //@ ensures \\fresh(\\result.a) \n" +
			"  Fresh m5() { \n" +
			"    return new Fresh(5); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_372() {
			this.runNegativeTest(new String[] {
			testsPath + "E.java", 
			"class E { \n" +
			"  boolean x, y, z; \n" +
			" \n" +
			"  //@ requires x ==> y ==> z; \n" +
			"  void m0() { \n" +
			"    if (x) { \n" +
			"      if (y) { \n" +
			"	//@ assert z; \n" +
			"      } else { \n" +
			"	//@ assert z;  // should generate warning \n" +
			"      } \n" +
			"    } else { \n" +
			"      //@ assert y;  // should generate warning \n" +
			"      //@ assert z;  // should generate warning \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires (x ==> y) ==> z; \n" +
			"  void m1(boolean t) { \n" +
			"    if (x) { \n" +
			"      if (y) { \n" +
			"	//@ assert z; \n" +
			"      } else { \n" +
			"	//@ assert z;  // should generate warning \n" +
			"      } \n" +
			"    } else if (t) { \n" +
			"      //@ assert y;  // should generate warning \n" +
			"    } else { \n" +
			"      //@ assert z; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires z <== y <== x; \n" +
			"  void m2() { \n" +
			"    if (x) { \n" +
			"      if (y) { \n" +
			"	//@ assert z; \n" +
			"      } else { \n" +
			"	//@ assert z;  // should generate warning \n" +
			"      } \n" +
			"    } else { \n" +
			"      //@ assert y;  // should generate warning \n" +
			"      //@ assert z;  // should generate warning \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  //@ requires z <== (y <== x); \n" +
			"  void m3(boolean t) { \n" +
			"    if (x) { \n" +
			"      if (y) { \n" +
			"	//@ assert z; \n" +
			"      } else { \n" +
			"	//@ assert z;  // should generate warning \n" +
			"      } \n" +
			"    } else if (t) { \n" +
			"      //@ assert y;  // should generate warning \n" +
			"    } else { \n" +
			"      //@ assert z; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void p(boolean t) { \n" +
			"    if (t) { \n" +
			"      //@ assert x <==> y <==> z <==> t <==> z <==> y <==> x; \n" +
			"      //@ assert x <=!=> y <=!=> z <=!=> t <=!=> z <=!=> y <=!=> x; \n" +
			"    } else { \n" +
			"      //@ assert x <==> y <=!=> z <==> t <==> z <==> y <==> x; \n" +
			"      //@ assert x <=!=> y <=!=> z <=!=> t <=!=> z <==> y <=!=> x; \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void q() { \n" +
			"    // the following should fail to verify: \n" +
			"    //@ assert y <=!=> x <==> y <==> x; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_373() {
			this.runNegativeTest(new String[] {
			testsPath + "D.java", 
			"class D { \n" +
			"  boolean b, c, d; \n" +
			" \n" +
			"  // The following are not allowed \n" +
			"  //@ invariant b ==> c <== d; \n" +
			"  //@ invariant b <== c ==> d; \n" +
			"  //@ invariant b ==> b <== b <== b ==> b ==> b <== b <== b ==> b ==> b <== b; \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_374() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"class C { \n" +
			"  C() {} //@ nowarn \n" +
			" \n" +
			"  boolean b, c, d; \n" +
			" \n" +
			"  //@ invariant b ==> c; \n" +
			"  //@ invariant b <== c; \n" +
			"  //@ invariant b <==> c; \n" +
			"  //@ invariant b <=!=> c; \n" +
			" \n" +
			"  int a[]; \n" +
			"  //@ invariant (\\forall int j; a[j] > 0) ==> (\\exists int j; a[j] > 0); \n" +
			"  //@ invariant (\\forall int j; a[j] > 0) <== (\\exists int j; a[j] > 0); \n" +
			"  //@ invariant (\\forall int j; a[j] > 0) <==> (\\exists int j; a[j] > 0); \n" +
			"  //@ invariant (\\forall int j; a[j] > 0) <=!=> (\\exists int j; a[j] > 0); \n" +
			" \n" +
			"  //@ invariant b ==> c ==> d; \n" +
			"  //@ invariant b <== c <== d; \n" +
			"  //@ invariant b <==> c <==> d; \n" +
			"  //@ invariant b <=!=> c <=!=> d; \n" +
			"   \n" +
			"  //@ invariant b ==> (c <== d); \n" +
			"  //@ invariant (b ==> c) <== d; \n" +
			"  //@ invariant b <== (c ==> d); \n" +
			"  //@ invariant (b <== c) ==> d; \n" +
			"   \n" +
			"  //@ invariant b <==> c <=!=> d; \n" +
			"  //@ invariant b <==> c <=!=> d; \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_375() {
			this.runNegativeTest(new String[] {
			testsPath + "NestedError.java", 
			"/** \n" +
			" ** This file tests parsing of nested escjava annotations \n" +
			" **/ \n" +
			" \n" +
			"class NestedError { \n" +
			" \n" +
			"    /* \n" +
			"     * level 2: \n" +
			"     */ \n" +
			" \n" +
			"    //@ ghost public int[] c //@ non_null //@non_null // error \n" +
			"    //@ ghost public int[] d //@ non_null //*non_null // error \n" +
			"    //@ ghost public int[] e //* non_null //@non_null \n" +
			" \n" +
			"    NestedError() { \n" +
			"      int[] a = new int[10]; \n" +
			"      //@ set c = a; \n" +
			"      //@ set d = a; \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_376() {
			this.runNegativeTest(new String[] {
			testsPath + "NormalError.java", 
			"/** \n" +
			" ** This file tests parsing of erroneous, normal escjava annotation comments \n" +
			" **/ \n" +
			" \n" +
			"class NormalError { \n" +
			" \n" +
			"    void wizard() { \n" +
			"	/*@(fobar*/      // error \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_377() {
			this.runNegativeTest(new String[] {
			testsPath + "JavaDocFatal2.java", 
			"/** \n" +
			" ** This file tests parsing of escjava annotations in javadoc comments \n" +
			" **/ \n" +
			" \n" +
			"class JavaDocFatal2 { \n" +
			" \n" +
			"    void standard() { \n" +
			" \n" +
			"      /** <esc>assert true</esc> \n" +
			"	* <esc>assume false</esc> \n" +
			"	* <esc>notAnEscPragma hello</esc>  <--- error */ \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_378() {
			this.runNegativeTest(new String[] {
			testsPath + "JavaDocFatal0.java", 
			"/** \n" +
			" ** This file tests parsing of escjava annotations in javadoc comments \n" +
			" **/ \n" +
			" \n" +
			"class JavaDocFatal0 { \n" +
			" \n" +
			"    void standard() { \n" +
			" \n" +
			"      /** <esc>notAnEscPragma hello</esc>  <--- error \n" +
			"	* <esc>assert true</esc> \n" +
			"	* <esc>assume false</esc> */ \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_379() {
			this.runNegativeTest(new String[] {
			testsPath + "Nested.java", 
			"/** \n" +
			" ** This file tests parsing of nested escjava annotations \n" +
			" **/ \n" +
			" \n" +
			"class Nested { \n" +
			" \n" +
			"    /* \n" +
			"     * level 1: \n" +
			"     */ \n" +
			" \n" +
			"    //@ ghost public int[] t //@ non_null \n" +
			"    //@ ghost public /*@non_null*/ int[] x \n" +
			"    //@ ghost public /**<esc>non_null</esc>*/ int[] y \n" +
			" \n" +
			"    /*@ ghost public int[] v //@ non_null */ \n" +
			"    //@ ghost public int[] w /** <esc>non_null</esc> */ \n" +
			"    //@ ghost public int[] a /** <esc></esc> */ \n" +
			" \n" +
			"    //*<esc> ghost public int[] b /*@non_null*/ </esc> \n" +
			" \n" +
			"    /*@ invariant a[1] > a[0] ; //@ nowarn \n" +
			"      invariant a[2] > a[1]  //@ nowarn \n" +
			"    */ \n" +
			" \n" +
			"    //@ ghost public /*@ non_null */ /*@ readable_if a[0] > 0 */ Nested r  \n" +
			" \n" +
			"    /* \n" +
			"     * level 2: \n" +
			"     */ \n" +
			" \n" +
			"    //@ ghost public int[] e //* non_null //@non_null \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_380() {
			this.runNegativeTest(new String[] {
			testsPath + "JavaDocFatal1.java", 
			"/** \n" +
			" ** This file tests parsing of escjava annotations in javadoc comments \n" +
			" **/ \n" +
			" \n" +
			"class JavaDocFatal1 { \n" +
			" \n" +
			"    void standard() { \n" +
			" \n" +
			"      /** <esc>assert true</esc> \n" +
			"	* <esc>notAnEscPragma hello</esc>  <--- error \n" +
			"	* <esc>assume false</esc> */ \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_381() {
			this.runNegativeTest(new String[] {
			testsPath + "Normal.java", 
			"/** \n" +
			" ** This file tests parsing of normal escjava annotation comments \n" +
			" **/ \n" +
			" \n" +
			"class Normal { \n" +
			" \n" +
			"    void standard() { \n" +
			" \n" +
			"	//@ assert true \n" +
			" \n" +
			"	/*@ assert true*/ \n" +
			"	/*@assert true*/ \n" +
			" \n" +
			"	/*@assume \"/*\"!=\"**\"*/ \n" +
			"    } \n" +
			" \n" +
			"    void wizard() { \n" +
			"	//@ assert true \n" +
			"	//@() assert true \n" +
			"	//@(++!!++) assert true \n" +
			"    } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_382() {
			this.runNegativeTest(new String[] {
			testsPath + "JavaDocCheck.java", 
			"/** \n" +
			" ** This file tests parsing of escjava annotations in javadoc comments \n" +
			" **/ \n" +
			" \n" +
			"class JavaDocCheck { \n" +
			" \n" +
			"  /** <esc>requires x == 0;</esc><esc>requires y == 1;   </esc> \n" +
			"    * \n" +
			"    * \n" +
			"    *  <esc> \n" +
			"    *       requires z == 2; \n" +
			"    *  </esc> \n" +
			"    **/ \n" +
			"  /** <esc>requires w \n" +
			"    * == 3;</esc> */ \n" +
			" \n" +
			"  // The following is not a Javadoc comment, so ESC/Java ignores what's \n" +
			"  // inside of it. \n" +
			"  //** <esc>ensures \\result == 8;</esc> \n" +
			"  int m(int x, int y, int z, int w) { \n" +
			"    //@ assert x == 0; \n" +
			"    //@ assert y == 1; \n" +
			"    //@ assert z == 2; \n" +
			"    //@ assert w == 3; \n" +
			"    return 10; \n" +
			"  } \n" +
			" \n" +
			"  int n() { \n" +
			"    // The following produces a warning, just to see that the file really \n" +
			"    // is being checked. \n" +
			"    //@ unreachable \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_383() {
			this.runNegativeTest(new String[] {
			testsPath + "JavaDoc.java", 
			"/** \n" +
			" ** This file tests parsing of escjava annotations in javadoc comments \n" +
			" **/ \n" +
			" \n" +
			"class JavaDoc { \n" +
			" \n" +
			"    void standard() { \n" +
			" \n" +
			"      /** <esc>assert true</esc> */ \n" +
			" \n" +
			"      /**<esc>assert true</esc>*/ \n" +
			"      /**anyoldjunk<esc>assert true</esc>canbehere*/ \n" +
			"      /**<escesc><esc>assert true</esc>*/ \n" +
			" \n" +
			"      //**<esc></esc>*/              //*<esc></esc> \n" +
			"      /** no esc comment */ \n" +
			" \n" +
			"      //* <esc>assert true         // no error, because not a JavaDoc comment \n" +
			"      /** <esc>assert true   */    // error \n" +
			"      /** <esc>assert true         // error */ \n" +
			"      /** <esc>assert true         // not an error  </esc> */ \n" +
			" \n" +
			"      /** <esc>assert true</esc> \n" +
			"	* <esc>assume true</esc> \n" +
			"	* <esc>assume false</esc> @ @ @ */ \n" +
			"    } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_384() {
			this.runNegativeTest(new String[] {
			testsPath + "ArraySubtypes.java", 
			"class ArraySubtypes { \n" +
			"  //@ requires a != null && a.length != 0; \n" +
			"  //@ requires a[0] != null && a[0].length != 0; \n" +
			"  //@ requires \\typeof(b) <: \\elemtype(\\typeof(a[0])); \n" +
			"  void m0(Object[][] a, Object b) { \n" +
			"    a[0][0] = b; \n" +
			"    // The following assert should fail because \"a\" may have \n" +
			"    // been equal to \"a[0]\" initially. \n" +
			"    /*@ assert a[0][0] == b; */  // this should fail \n" +
			"  } \n" +
			" \n" +
			"  //@ requires a != null && a.length != 0; \n" +
			"  //@ requires a[0] == a; \n" +
			"  //@ requires \\typeof(b) <: \\elemtype(\\typeof(a)); \n" +
			"  void m1(Object[][] a, Object b) { \n" +
			"    //@ assert \\typeof(a) <: \\elemtype(\\typeof(a)); \n" +
			"    a[0] = a; \n" +
			"    a[0][0] = b; \n" +
			"    /*@ assert a[0][0] == b; */  // this should fail \n" +
			"  } \n" +
			" \n" +
			"  //@ requires a != null && a.length != 0; \n" +
			"  //@ requires \\typeof(a) <: \\elemtype(\\typeof(a)); \n" +
			"  //@ requires \\typeof(b) <: \\elemtype(\\typeof(a)); \n" +
			"  void m2(Object[][] a, Object b) { \n" +
			"    a[0] = a; \n" +
			"    a[0][0] = b; \n" +
			"    /*@ assert a[0][0] == b; */  // this should fail \n" +
			"  } \n" +
			" \n" +
			"  //@ requires a != null && a.length != 0; \n" +
			"  //@ requires \\typeof(a) == \\type(Object[][]); \n" +
			"  //@ requires \\typeof(b) <: \\elemtype(\\typeof(a)); \n" +
			"  void m3(Object[][] a, Object b) { \n" +
			"    //@ assert \\typeof(a) <: \\elemtype(\\typeof(a)); \n" +
			"    a[0] = a; \n" +
			"    a[0][0] = b; \n" +
			"    /*@ assert a[0][0] == b; */  // this should fail \n" +
			"  } \n" +
			" \n" +
			"  //@ requires a != null && a.length != 0; \n" +
			"  //@ requires \\typeof(a) == \\type(Object[][]); \n" +
			"  //@ requires \\typeof(b) <: \\type(Object[]); \n" +
			"  void m4(Object[][] a, Object b) { \n" +
			"    /* This example shows exactly how \"m0()\" may fail */ \n" +
			"    a[0] = a; \n" +
			"    a[0][0] = b; \n" +
			"    //@ assert a[0] == b; \n" +
			"    /*@ assert a[0][0] == b; */  // this should fail \n" +
			"  } \n" +
			" \n" +
			"  //@ requires a != null && a.length != 0; \n" +
			"  //@ requires a[0] != null && a[0].length != 0; \n" +
			"  //@ requires \\typeof(b) <: \\elemtype(\\typeof(a[0])); \n" +
			"  void m5(Object[][] a, Object b) { \n" +
			"    if (a != a[0] || a[0] == b) { \n" +
			"      a[0][0] = b; \n" +
			"      /*@ assert a[0][0] == b; */  // this should succeed \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m6(Object b) { \n" +
			"    Object[][] a = new Object[12][40]; \n" +
			"    a[0][0] = b; \n" +
			"    /*@ assert a[0][0] == b; */  // this should succeed \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_385() {
			this.runNegativeTest(new String[] {
			testsPath + "Dttfsa.java", 
			"class Dttfsa { \n" +
			"  void m0(int x) { \n" +
			"    // The following assert should fail to verify, because nothing is known \n" +
			"    // about function \"dude\". \n" +
			"    //@ assert (boolean)\\dttfsa(boolean, \"dude\", x-1, x+1); \n" +
			"  } \n" +
			" \n" +
			"  /*@ requires (\\forall int a, b; a < b ==> \n" +
			"                                (boolean)\\dttfsa(boolean, \"dude\", a, b)); */ \n" +
			"  void m1(int x) { \n" +
			"    //@ assert (boolean)\\dttfsa(boolean, \"dude\", x-1, x+1); \n" +
			"  } \n" +
			" \n" +
			"  void m2(int x) { \n" +
			"    //@ assert \\dttfsa(boolean, \"is\", x, \\dttfsa(\\TYPE, \"T_int\")); \n" +
			"  } \n" +
			" \n" +
			"  void m3(int x) { \n" +
			"    // The following assert should fail to verify, because ESC/Java's \n" +
			"    // logic doesn't include anything that says that every \"int\" is a \"double\". \n" +
			"    //@ assert \\dttfsa(boolean, \"is\", x, \\dttfsa(\\TYPE, \"T_double\")); \n" +
			"  } \n" +
			" \n" +
			"  void m4(int x) { \n" +
			"    //@ assert \\dttfsa(Object, \"identity\", x) == \\dttfsa(Object[], \"identity\", x); \n" +
			"  } \n" +
			" \n" +
			"  void m5(int x) { \n" +
			"    // This tests that the resulting S-expressions are predicates, not terms. \n" +
			"    //@ assert \\dttfsa(boolean, \"<\", x-1, x+1); \n" +
			"    //@ assert !\\dttfsa(boolean, \"<\", x-1, x+1);  // fails \n" +
			"  } \n" +
			" \n" +
			"  void m6(int x) { \n" +
			"    // see m5 \n" +
			"    //@ assert !\\dttfsa(boolean, \">\", x-1, x+1); \n" +
			"    //@ assert \\dttfsa(boolean, \">\", x-1, x+1);  // fails \n" +
			"  } \n" +
			" \n" +
			"  //@ requires b; \n" +
			"  void m7a(boolean b) { \n" +
			"    // This tests that \\dttfsa expressions get translated as terms, with \n" +
			"    // a surrounding \"(EQ |@true| ...)\" to make it a predicate. \n" +
			"    // (If this is not the case, Simplify will complain, breaking this test \n" +
			"    // case.) \n" +
			"    //@ assert (boolean)\\dttfsa(boolean, \"identity\", b); \n" +
			"    //@ assert (boolean)!\\dttfsa(boolean, \"identity\", b); // fails \n" +
			"  } \n" +
			" \n" +
			"  //@ requires b; \n" +
			"  void m7b(boolean b) { \n" +
			"    // see m7a \n" +
			"    //@ assert !(boolean)\\dttfsa(boolean, \"identity\", b); // fails \n" +
			"  } \n" +
			" \n" +
			"  //@ requires b; \n" +
			"  void m8a(boolean b) { \n" +
			"    // see m7a \n" +
			"    //@ assert (boolean)\\dttfsa(boolean, \"identity\", !b); // fails \n" +
			"  } \n" +
			" \n" +
			"  //@ requires b; \n" +
			"  void m8b(boolean b) { \n" +
			"    // see m7a \n" +
			"    //@ assert !(boolean)\\dttfsa(boolean, \"identity\", !b); \n" +
			"    //@ assert (boolean)!\\dttfsa(boolean, \"identity\", !b); // fails \n" +
			"  } \n" +
			" \n" +
			"  void m9() { \n" +
			"    //@ assert \\dttfsa(boolean, \"(EQ (+ 3 2) 5)\"); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_386() {
			this.runNegativeTest(new String[] {
			testsPath + "DttfsaTypecheck.java", 
			"class DttfsaTypecheck { \n" +
			"  int x; \n" +
			" \n" +
			"  //@ invariant \\dttfsa(int, x); // fails (expecting String literal) \n" +
			"  //@ invariant \\dttfsa(Object[], x); // fails (expecting String literal) \n" +
			"  //@ invariant \\dttfsa(int, \"identity\"); // fails (expecting 3 args) \n" +
			"  //@ invariant \\dttfsa(int, \"identity\", x, x); // fails (expecting 3 args) \n" +
			" \n" +
			"  //@ invariant \\dttfsa(int, \"f\", x); // fails (expecting boolean) \n" +
			"  //@ invariant \\dttfsa(void, \"f\", x); // fails (expecting boolean) \n" +
			"  //@ invariant \\dttfsa(int, \"identity\", x); // fails (expecting boolean) \n" +
			"  //@ invariant \\dttfsa(boolean, \"identity\", \\dttfsa(int, \"f\", x)); \n" +
			"  /*@ invariant \\dttfsa(boolean, \"EQ\", \n" +
			"                       \\dttfsa(void, \"f\", x), \n" +
			"		       \\dttfsa(Object[], \"g\", x, x, x+x, x-x, 3, true, null)); \n" +
			"  */ \n" +
			" \n" +
			"  //@ invariant \\dttfsa(boolean, \"f\", x, y);  // fails (doesn't know y) \n" +
			" \n" +
			"  void m() { \n" +
			"    //@ assert \\dttfsa(boolean, \"(EQ (fact (+ x 1)) (* (+ x 1) (fact x)))\"); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_387() {
			this.runNegativeTest(new String[] {
			testsPath + "DttfsaDoesntEvenParse2.java", 
			"class DttfsaDoesntEvenParse2 { \n" +
			"  int x; \n" +
			"  //@ invariant \\dttfsa(x, x); // fails (expecting type) \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_388() {
			this.runNegativeTest(new String[] {
			testsPath + "DttfsaDoesntEvenParse3.java", 
			"class DttfsaDoesntEvenParse3 { \n" +
			"  int x; \n" +
			"  //@ invariant \\dttfsa(UndeclaredType[], x); // fails (expecting type) \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_389() {
			this.runNegativeTest(new String[] {
			testsPath + "DttfsaDoesntEvenParse0.java", 
			"class DttfsaDoesntEvenParse0 { \n" +
			"  //@ invariant \\dttfsa(); // fails (too few arguments) \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_390() {
			this.runNegativeTest(new String[] {
			testsPath + "DttfsaDoesntEvenParse1.java", 
			"class DttfsaDoesntEvenParse1 { \n" +
			"  //@ invariant \\dttfsa(int); // fails (too few arguments) \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_391() {
			this.runNegativeTest(new String[] {
			testsPath + "A.java", 
			"// static methods with bodies \n" +
			" \n" +
			"public class A { \n" +
			" \n" +
			"  /*@ requires i >= 0; \n" +
			"    @ ensures \\result == (i/i)*2; // divZero warning \n" +
			"    @*/ \n" +
			"  public static int test0(int i) { \n" +
			"    return 2; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i > 0; \n" +
			"    @  ensures \\result == (i/i)*2; // no divZero warning because of precondition \n" +
			"    @*/ \n" +
			"  public static int test1(int i) { \n" +
			"    return 2; \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ exceptional_behavior \n" +
			"    @  requires i<0; \n" +
			"    @  signals (RuntimeException e) i<0; // null(charArray.owner) because of invariant \n" +
			"    @*/ \n" +
			"  public static int test2(int i) throws RuntimeException { \n" +
			"    throw new RuntimeException(); \n" +
			"  } \n" +
			" \n" +
			"  /*@ exceptional_behavior \n" +
			"    @  requires i<0; \n" +
			"    @  signals (RuntimeException e) i/i == i/i; // no divZero warning because of precondition \n" +
			"    @                                           // null(charArray.owner) because of invariant \n" +
			"    @*/ \n" +
			"  public static int test3(int i) throws RuntimeException { \n" +
			"    throw new RuntimeException(); \n" +
			"  } \n" +
			" \n" +
			"  /*@ exceptional_behavior \n" +
			"    @  requires i <= 0; \n" +
			"    @  signals (RuntimeException e) i/i == i/i; // divZero warning \n" +
			"    @                                           // null(charArray.owner) because of invariant \n" +
			"    @*/ \n" +
			"  public static int test4(int i) throws RuntimeException { \n" +
			"    throw new RuntimeException(); \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i>=0; \n" +
			"    @  ensures \\result == (i/i)*2; // divZero warning \n" +
			"    @ also exceptional_behavior \n" +
			"    @  requires i<0; \n" +
			"    @  signals (RuntimeException e) i/i == i/i; // no divZero because of precondition \n" +
			"    @                                           // null(charArray.owner) because of invariant \n" +
			"    @*/ \n" +
			"  public static int test5(int i) throws RuntimeException { \n" +
			"    if(i<0) \n" +
			"      throw new RuntimeException(); \n" +
			"    return 2;       \n" +
			"  } // Postcondition not established warning \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires i>0; \n" +
			"    @  ensures \\result == (i/i)*2; // no divZero warning because of precondition \n" +
			"    @ also exceptional_behavior \n" +
			"    @  requires i<=0; \n" +
			"    @  signals (RuntimeException e) i/i == i/i; // divZero warnings \n" +
			"    @                                           // null(charArray.owner) because of invariant     \n" +
			"    @*/ \n" +
			"  public static int test6(int i) throws RuntimeException { \n" +
			"    if(i<=0) \n" +
			"      throw new RuntimeException(); \n" +
			"    return (i/i)*2; \n" +
			"  } \n" +
			"	 \n" +
			"  //@ requires i/i==i/i; // expect: ZeroDiv \n" +
			"  public static int test7(int i) { \n" +
			"    return (i/i)*2; \n" +
			"  } \n" +
			" \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_392() {
			this.runNegativeTest(new String[] {
			testsPath + "FormalModifiers.java", 
			"/** \n" +
			" ** Test that we can put escjava modifiers after formal parameters \n" +
			" **/ \n" +
			" \n" +
			"class FormalModifiers { \n" +
			"    //@ pure \n" +
			"    void foo (String x /*@non_null*/, \n" +
			"	      Object z[] /*@non_null*/, \n" +
			"	      int[] q /*@non_null*/ /*@non_null*/) {} \n" +
			"    //@ pure \n" +
			"    void bar (/*@non_null*/ String a /*@non_null*/) {} \n" +
			"    //@ pure \n" +
			"    void b1 (int b) {} \n" +
			"    //@ pure \n" +
			"    void b2 (/*@non_null*/ String b) {} \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_393() {
			this.runNegativeTest(new String[] {
			testsPath + "State.java", 
			"abstract public class State { \n" +
			" \n" +
			"  /*@ non_null @*/ int[] vector; \n" +
			" \n" +
			"  protected State(/*@ non_null @*/ int[] vector) { \n" +
			"    //@ set owner = this \n" +
			"    this.vector = vector; \n" +
			"  }  // error: OwnerNull \n" +
			" \n" +
			"  protected State(Object x) { \n" +
			"    if (x instanceof int[]) { \n" +
			"      //@ set owner = x; \n" +
			"      this.vector = (int[])x; \n" +
			"    } else { \n" +
			"      this.vector = new int[10]; \n" +
			"    } \n" +
			"  }  // error: OwnerNull on one path \n" +
			" \n" +
			"  //@ requires 0 <= y; \n" +
			"  protected State(Object x, int y) { \n" +
			"    this.vector = new int[y]; \n" +
			"    if (x instanceof int[]) { \n" +
			"      //@ set x.owner = this;  // no confusion that 'x' might be 'this' \n" +
			"      this.vector = (int[])x; \n" +
			"    } else if (x != null) { \n" +
			"      //@ set x.owner = this;  // no confusion that 'x' might be 'this' \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_394() {
			this.runNegativeTest(new String[] {
			testsPath + "InnerClassTest.java", 
			"public class InnerClassTest {		 \n" +
			"	private char blankChar = ' ';		 \n" +
			"	private boolean isTrue = true;		 \n" +
			"			 \n" +
			"	private int followUpCode;		 \n" +
			"					 \n" +
			"	public char getBlankChar(){		 \n" +
			"		return blankChar;		 \n" +
			"	}		 \n" +
			"				 \n" +
			"	public void setBlankChar(char inputChar) {		 \n" +
			"		this.blankChar = inputChar;		 \n" +
			"	}		 \n" +
			"			 \n" +
			"	// Problems with ESC/Java2 when this method is not commented out,		 \n" +
			"	// but only on linux and windows, not on Mac OS X		 \n" +
			"	public void setBlankChar(String inputChars) {		 \n" +
			"		this.blankChar = inputChars.charAt(0);		 \n" +
			"	}		 \n" +		
			"		 \n" +
			"	public boolean isTrue() {		 \n" +
			"		return isTrue;		 \n" +
			"	}		 \n" +
			"		 \n" +
			"	public void setTrue(boolean isTrue) {		 \n" +
			"		this.isTrue = isTrue;		 \n" +
			"	}		 \n" +
			"		 \n" +
			"	public int getFollowUpCode() {		 \n" +
			"		return followUpCode;		 \n" +
			"	}		 \n" +
			"		 \n" +
			"	public void setFollowUpCode(int followUpCode) {		 \n" +
			"		this.followUpCode = followUpCode;		 \n" +
			"	}		 \n" +
			"			 \n" +
			"}		 \n" 
			}, "ERROR");
			}

			public void test_395() {
			this.runNegativeTest(new String[] {
			testsPath + "Test307.java", 
			"public class Test307 {		 \n" +
			"	final /*@non_null*/String s444[/*#@nullable*/] = new String[3];		 \n" +
			"			 \n" +
			"	void m111() {		 \n" +
			"		String s = \"\";		 \n" +
			"		for(int i = 0; i < s444.length; i++)		 \n" +
			"			s += s444[i]; // ok		 \n" +
			"	}		 \n" +
			"	void m333() {		 \n" +
			"		int s = 0;		 \n" +
			"		for(int i = 0; i < s444.length; i++)		 \n" +
			"			s += s444[i].length(); // error		 \n" +
			"	}		 \n" +
			"		 \n" +
			"	//@ invariant (\\forall int i; s444.length == s444.length);		 \n" +
			"	/*@ invariant (\\forall int i; 0 <= i && i < s444.length;		 \n" +
			"	  @ // FIXME: THE NEXT LINE IS DISABLED DUE TO A BUG IN ESC.		 \n" +
			"	  @ //			s444[i] == s444[i]); // NO ERROR SHOULD BE REPORTED HERE.		 \n" +
			"	  @ 			true);		 \n" +
			"	  @*/		 \n" +
			"}		 \n" 
			}, "ERROR");
			}

			public void test_396() {
			this.runNegativeTest(new String[] {
			testsPath + "C.java", 
			"// @see Ticket #28 : NullPointerException thrown with @pure modified comes before @modifies spec		 \n" +
			"		 \n" +
			"public class C {		 \n" +
			"		 \n" +
			"    /*@pure*/		 \n" +
			"    //@ modifies \\nothing;		 \n" +
			"	public void foo() {		 \n" +
			"	}		 \n" +
			"		 \n" +
			" 	public void bar() {		 \n" +
			"		foo();		 \n" +
			"	}		 \n" +
			"}		 \n" 
			}, "ERROR");
			}

			public void test_397() {
			this.runNegativeTest(new String[] {
			testsPath + "E1.java", 
			"public class E1 { \n" +
			" \n" +
			"  //@ invariant this.f>=88;  \n" +
			"  //@ invariant f/f == f/f; // divZero warning \n" +
			"  public int f; \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires ff>=99; \n" +
			"    @  ensures this.f==ff; \n" +
			"    @*/ \n" +
			"  public E1(int ff) { \n" +
			"    this.f=ff; \n" +
			"  } \n" +
			" \n" +
			"  /*@ ensures \\result == this.f+1; \n" +
			"    @*/ \n" +
			"  public int test0() { \n" +
			"    return this.f+1; \n" +
			"  }  \n" +
			" \n" +
			"  /*@ requires ff>=99; \n" +
			"    @ ensures this.f == ff; \n" +
			"    @*/ \n" +
			"  public int test1(int ff) { \n" +
			"    this.f=ff; \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires ff>=99; \n" +
			"    @  ensures this.f==ff; \n" +
			"    @*/ \n" +
			"  public void test2(int ff) { \n" +
			"    this.f=ff; \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires ff>=99; \n" +
			"    @  ensures this.f==ff; \n" +
			"    @*/ \n" +
			"  public void test3(int ff) { \n" +
			"    this.f=ff; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_398() {
			this.runNegativeTest(new String[] {
			testsPath + "E2.java", 
			"public class E2 { \n" +
			" \n" +
			"  //@ invariant a.length>0; // null(a) warning \n" +
			"  public int [] a; \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires aa.length>0; //null(aa) warning \n" +
			"    @  ensures this.a==aa; \n" +
			"    @*/ \n" +
			"  public E2(int [] aa) { \n" +
			"    this.a=aa; \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires aa.length>0; //null(aa) warning \n" +
			"    @  ensures this.a==aa; \n" +
			"    @*/ \n" +
			"  public void test2(int [] aa) { \n" +
			"    this.a=aa; \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires aa.length>0; \n" +
			"    @  ensures this.a==aa; \n" +
			"    @*/ \n" +
			"  public void test3(/*@non_null*/int [] aa) { \n" +
			"    this.a=aa; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_399() {
			this.runNegativeTest(new String[] {
			testsPath + "A.java", 
			"public class A extends C { \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_400() {
			this.runNegativeTest(new String[] {
			testsPath + "DefIf.java", 
			"class DefIf { \n" +
			"  int f; \n" +
			"  int h /*@ readable_if f == 2 */; \n" +
			"   \n" +
			"  void m0() { \n" +
			"    int x = 0; \n" +
			"    if (this.f == 2) { \n" +
			"      x = this.h;  // okay \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  void m1() { \n" +
			"    int x = 0; \n" +
			"    x = this.h;  // illegal access \n" +
			"  } \n" +
			"   \n" +
			"  void m2(DefIf d) { \n" +
			"    int x = 0; \n" +
			"    if (d != null && d.f == 2) { \n" +
			"      x = d.h;  // okay \n" +
			"      Object o = d; \n" +
			"      x = ((DefIf)o).h;  // okay \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m3(DefIf d) { \n" +
			"    int x = 0; \n" +
			"    if (d != null && this.f == 2) { \n" +
			"      x = d.h;  // illegal access \n" +
			"    } \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_401() {
			this.runNegativeTest(new String[] {
			testsPath + "DefIf.java", 
			"class MonitoredBy { \n" +
			"  /*@ non_null */ Object f = new Object(); \n" +
			"  int h /*@ monitored_by f */; \n" +
			" \n" +
			"  void m0() { \n" +
			"    int x = 0; \n" +
			"    synchronized (this.f) { \n" +
			"      x = this.h;  // okay \n" +
			"      this.h = x;  // okay \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  void m1r() { \n" +
			"    int x = 0; \n" +
			"    x = this.h;  // illegal access \n" +
			"  } \n" +
			"   \n" +
			"  void m1w() { \n" +
			"    int x = 0; \n" +
			"    this.h = x;  // illegal access \n" +
			"  } \n" +
			"   \n" +
			"  void m2(/*@ non_null */ MonitoredBy d) { \n" +
			"    int x = 0; \n" +
			"    synchronized (d.f) { \n" +
			"      x = d.h;  // okay \n" +
			"      d.h = x;  // okay \n" +
			"      Object o = d; \n" +
			"      x = ((MonitoredBy)o).h;  // okay \n" +
			"      ((MonitoredBy)o).h = x;  // okay \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m3r(/*@ non_null */ MonitoredBy d) { \n" +
			"    int x = 0; \n" +
			"    synchronized (this.f) { \n" +
			"      x = d.h;  // illegal access \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m3w(/*@ non_null */ MonitoredBy d) { \n" +
			"    int x = 0; \n" +
			"    synchronized (this.f) { \n" +
			"      d.h = x;  // illegal access \n" +
			"    } \n" +
			"  } \n" +
			"} \n" +
			" \n" 
			}, "ERROR");
			}

			public void test_402() {
			this.runNegativeTest(new String[] {
			testsPath + "DefIf.java", 
			"class Monitored { \n" +
			"  /*@ monitored */ int h; \n" +
			" \n" +
			"  void m0() { \n" +
			"    int x = 0; \n" +
			"    synchronized (this) { \n" +
			"      x = this.h;  // okay \n" +
			"      this.h = x;  // okay \n" +
			"    } \n" +
			"  } \n" +
			"   \n" +
			"  void m1r() { \n" +
			"    int x = 0; \n" +
			"    x = this.h;  // illegal access \n" +
			"  } \n" +
			"   \n" +
			"  void m1w() { \n" +
			"    int x = 0; \n" +
			"    this.h = x;  // illegal access \n" +
			"  } \n" +
			"   \n" +
			"  void m2(/*@ non_null */ Monitored d) { \n" +
			"    int x = 0; \n" +
			"    synchronized (d) { \n" +
			"      x = d.h;  // okay \n" +
			"      d.h = x;  // okay \n" +
			"      Object o = d; \n" +
			"      x = ((Monitored)o).h;  // okay \n" +
			"      ((Monitored)o).h = x;  // okay \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m3r(/*@ non_null */ Monitored d) { \n" +
			"    int x = 0; \n" +
			"    synchronized (this) { \n" +
			"      x = d.h;  // illegal access \n" +
			"    } \n" +
			"  } \n" +
			" \n" +
			"  void m3w(/*@ non_null */ Monitored d) { \n" +
			"    int x = 0; \n" +
			"    synchronized (this) { \n" +
			"      d.h = x;  // illegal access \n" +
			"    } \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_403() {
			this.runNegativeTest(new String[] {
			testsPath + "O124.java", 
			"class O124 { \n" +
			"  /* tests invariant optimizations O1, O2 and O4. All are tested in by \n" +
			"     the GC for the chk() methods. \n" +
			"   \n" +
			"     after call, assumption is forall s. (Jpre[s] || allocated[s]) => Jpost[s] \n" +
			"      \n" +
			"     O1. if vars of inv are not modified, drop Jpre[s] \n" +
			"     O2. if fresh is not mentioned in spec and not constructor call, \n" +
			"         don't bump alloc, and drop \"allocated[s]\" \n" +
			" \n" +
			"     O4. at end of body only assert invariants whose vars are modified \n" +
			"  */ \n" +
			" \n" +
			" \n" +
			"  int i,j; \n" +
			" \n" +
			"  //@ invariant i>0 \n" +
			"  //@ invariant j>0 \n" +
			" \n" +
			"  O124() { \n" +
			"    i=1; \n" +
			"    j=1; \n" +
			"  } \n" +
			" \n" +
			"  //@ modifies i \n" +
			"  void modi() { \n" +
			"    i=2; \n" +
			"  } \n" +
			" \n" +
			"  void chk() { \n" +
			"    modi(); \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_404() {
			this.runNegativeTest(new String[] {
			testsPath + "E.java", 
			"public class E { \n" +
			" \n" +
			"  //@ invariant this.f>=88;  \n" +
			"  //@ invariant f/f == f/f; // divZero warning \n" +
			"  public int f; \n" +
			" \n" +
			"  //@ invariant a.length>0; // null(a) warning \n" +
			"  public int [] a; \n" +
			" \n" +
			"  /*@ ensures \\result == this.f+1; \n" +
			"    @*/ \n" +
			"  public int test0() { \n" +
			"    return this.f+1; \n" +
			"  }  \n" +
			" \n" +
			"  /*@ requires ff>=99; \n" +
			"    @ ensures this.f == ff; \n" +
			"    @*/ \n" +
			"  public int test1(int ff) { \n" +
			"    this.f=ff; \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires ff>=99; \n" +
			"    @  requires aa.length>0; //null(aa) warning \n" +
			"    @  ensures this.f==ff; \n" +
			"    @  ensures this.a==aa; \n" +
			"    @*/ \n" +
			"  public void test2(int ff, int [] aa) { \n" +
			"    this.f=ff; \n" +
			"    this.a=aa; \n" +
			"  } \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires ff>=99; \n" +
			"    @  requires aa.length>0; \n" +
			"    @  ensures this.f==ff; \n" +
			"    @  ensures this.a==aa; \n" +
			"    @*/ \n" +
			"  public void test3(int ff, /*@non_null*/int [] aa) { \n" +
			"    this.f=ff; \n" +
			"    this.a=aa; \n" +
			"  } \n" +
			" \n" +
			" \n" +
			"  /*@ normal_behavior \n" +
			"    @  requires ff>=99; \n" +
			"    @  requires aa.length>0; //null(aa) warning \n" +
			"    @  ensures this.f==ff; \n" +
			"    @  ensures this.a==aa; \n" +
			"    @*/ \n" +
			"  public E(int ff, int [] aa) { \n" +
			"    this.f=ff; \n" +
			"    this.a=aa; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}

			public void test_405() {
			this.runNegativeTest(new String[] {
			testsPath + "TexasSubstitution.java", 
			"// This test file performs a rudimentary check that the \n" +
			"// formal parameters mentioned in a modifies clause are \n" +
			"// replaced by the actual parameters of a call. \n" +
			" \n" +
			"// Our checker once did this incorrectly.  The name of \n" +
			"// the class in this test file is explained by the fact that \n" +
			"// the error was discovered during a private demo of ESC/Java \n" +
			"// at POPL'99 in San Antonio, TX. \n" +
			" \n" +
			"class TexasSubstitution { \n" +
			"  int n; \n" +
			" \n" +
			"  //@ modifies n; \n" +
			"  void m() { \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x != null && x != this; \n" +
			"  void mGood(TexasSubstitution x) { \n" +
			"    int nx = x.n; \n" +
			"    int nthis = this.n; \n" +
			"    x.m(); \n" +
			"    // The following line should generate no warning \n" +
			"    //@ assert nthis == this.n; \n" +
			"  } \n" +
			" \n" +
			"  //@ requires x != null && x != this; \n" +
			"  void mBad(TexasSubstitution x) { \n" +
			"    int nx = x.n; \n" +
			"    int nthis = this.n; \n" +
			"    x.m(); \n" +
			"    // The following line should generate a warning \n" +
			"    //@ assert nx == x.n; \n" +
			"  } \n" +
			"} \n" 
			}, "ERROR");
			}
		
}
