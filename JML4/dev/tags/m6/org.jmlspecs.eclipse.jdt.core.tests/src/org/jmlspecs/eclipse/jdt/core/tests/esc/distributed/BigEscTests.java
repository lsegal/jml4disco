package org.jmlspecs.eclipse.jdt.core.tests.esc.distributed;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.PostProcessor;
import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcDistributed;

public class BigEscTests extends AbstractRegressionTest {
		
	public BigEscTests(String name) {
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
		options.put(CompilerOptions.OPTION_ReportNonStaticAccessToStatic, CompilerOptions.IGNORE);		
		options.put(JmlCompilerOptions.OPTION_EscDistributedPropertiesFile, "proverCoordinatorUrls.properties");
		options.put(JmlCompilerOptions.OPTION_EscProverStrategy, ProveVcDistributed.getName());
		return options;
	}
	private final String testsPath = "tests" + '\\' + "esc" + '\\';

	public void test_000_assertFalse() {
		//left out ArrayTests._test_0010_returnArray 
		this.runNegativeTest(new String[] {
				testsPath + "X.java",
				"package tests.esc;\n" +
				"public class X {\n" + 
				" //------ARRAYTESTS----1 TO 8------------------\n" +
				"   //@ requires n.length >= 4;\n" + 
				"   //@ ensures  \\result == n[3];\n" + 
				"   public int m1(int[] n) {\n" + 
				"      return n[3];\n" + 
				"   }\n" +
				"   //@ ensures \\result == \\old(n[2]) + 1;\n" + 
				"   public int m2(int[] n) {\n" + 
				"      int result = n[2] + 1;\n" + 
				"      n[2] = 42;\n" + 
				"      return result;\n" + 
				"   }\n" + 		
				"   //@ ensures \\result == 42;\n" + 
				"   public int m3(int[] n) {\n" + 
				"      n[2] = 42;\n" + 
				"      return n[2];\n" + 
				"   }\n" + 		
				"   //@ ensures n[2] == 42 && \\result == 41;\n" + 
				"   public int m4(int[] n) {\n" + 
				"      n[2] = 41;\n" + 
				"      return n[2]++;\n" + 
				"   }\n" + 	
				"   //@ ensures n[2] == \\old(n[2]) + 1;\n" + 
				"   public void m5(int[] n) {\n" + 
				"      n[2] += 1;\n" + 
				"   }\n" + 	
				"   //@ requires n.length >= 4;\n" + 
				"   //@ ensures  \\result == n[3];\n" + 
				"   public int m6(int[] n) {\n" + 
				"      return n[3];\n" + 
				"   }\n" + 
				"   public int m7(int[] m) {\n" + 
				"      return m1(m);\n" + 
				"   }\n" + 		
				"   public void m8(int[] n) {\n" + 
				"      assert n.length >= 0;\n" + 
				"   }\n" + 	
				" //------FieldTests----9 TO 18------------------\n" +
				"   public int n9;\n" + 
				"   //@ ensures \\result == n9 + 1;\n" + 
				"   public int m9() {\n" + 
				"      return n9+1;\n" + 
				"   }\n" + 
				"   public int n10;\n" + 
				"   //@ ensures \\result == \\old(n10) + 1;\n" + 
				"   public int m10() {\n" + 
				"      return n10+1;\n" + 
				"   }\n" + 	
				"//   public int n11;\n" + 
				"//   //@ ensures n11 == \\old(n11) + 1;\n" + 
				"//   public void m11() {\n" + 
				"//      n11 = n11 + 1;\n" + 
				"//   }\n" + 	
				"   public int n12;\n" + 
				"   //@ ensures n12 == \\old(n12) + 1;\n" + 
				"   //@ ensures \\result == n12 - 1;\n" + 
				"   public int m12() {\n" + 
				"      return n12++;\n" + 
				"   }\n" + 	
				"//   public int n13;\n" + 
				"//   //@ ensures n13 == \\old(n13) + 1;\n" + 
				"//   public void m13() {\n" + 
				"//      n13 += 1;\n" + 
				"//   }\n" +
				"   public static int n14;\n" + 
				"   //@ ensures n14 == \\old(n14) + 1;\n" + 
				"   public void m14() {\n" + 
				"      n14++;\n" + 
				"   }\n" + 
				"   public int n15;\n" + 
				"   //@ ensures n15 == \\old(n15) + 1;\n" + 
				"   public void m15() {\n" + 
				"      this.n15++;\n" + 
				"   }\n" + 	
				"//   public int n16;\n" + 
				"//   //@ ensures x.n16 == \\old(this.n16) + 1;\n" + 
				"//   public void m16(X x) {\n" + 
				"//      x.n16 = this.n16 + 1;\n" + 
				"//   }\n" + 
				"   public static int n17;\n" + 
				"   //@ ensures x.n17 == \\old(this.n17) + 1;\n" + 
				"   public void m17(X x) {\n" + 
				"      x.n17 = this.n17 + 1;\n" + 
				"   }\n" + 	
				"   public static int n18;\n" + 
				"   //@ ensures n18 == \\old(n18) + 1;\n" + 
				"   public void m18(X x) {\n" + 
				"      x.n18 = this.n18 + 1;\n" + 
				"   }\n" + 	
				" //------InitialTests----19 TO ------------------\n" +
				"   public void m19() {\n" + 
				"      //@ assert false;\n" + 
				"   }\n" +
				"   public void m20() {\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 			
				"   public void m21() {\n" + 
				"      //@ assume false;\n" + 
				"   }\n" + 		
				"   public void m22() {\n" + 
				"      //@ assume true;\n" + 
				"   }\n" + 		
				"   public void m23(boolean b) {\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 		
				"   public void m24() {\n" + 
				"      //@ assume true;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 	
				"   public void m25() {\n" + 
				"      //@ assume true;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m26() {\n" + 
				"      //@ assume false;\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 	
				"   public void m27() {\n" + 
				"      //@ assume false;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m28() {\n" + 
				"      //@ assert false;\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 	
				"   public void m29() {\n" + 
				"      //@ assert false && false;\n" + 
				"   }\n" + 
				"   public void m30() {\n" + 
				"      //@ assert false & false;\n" + 
				"   }\n" + 		
				"   public void m31() {\n" + 
				"      //@ assert false || false;\n" + 
				"   }\n" + 	
				"   public void m32() {\n" + 
				"      //@ assert false && (false || false);\n" + 
				"   }\n" + 
				"   public void m33() {\n" + 
				"      //@ assert false & (false | false);\n" + 
				"   }\n" + 	
				"   public void m34() {\n" + 
				"      //@ assert (false | false) & false;\n" + 
				"   }\n" + 
				"   public void m35() {\n" + 
				"      //@ assert (false || false) && false;\n" + 
				"   }\n" + 	
				"   public void m36() {\n" + 
				"      //@ assert (true ? true : true);\n" + 
				"   }\n" + 
				"   public void m37() {\n" + 
				"      //@ assert (true ? true : false);\n" + 
				"   }\n" + 
				"   public void m38() {\n" + 
				"      //@ assert (true ? false : true);\n" + 
				"   }\n" + 
				"   public void m39() {\n" + 
				"      //@ assert (true ? false : false);\n" + 
				"   }\n" + 
				"   public void m40() {\n" + 
				"      //@ assert (false ? true : true);\n" + 
				"   }\n" + 
				"   public void m41() {\n" + 
				"      //@ assert (false ? true : false);\n" + 
				"   }\n" + 
				"   public void m42() {\n" + 
				"      //@ assert (false ? false : true);\n" + 
				"   }\n" + 
				"   public void m43() {\n" + 
				"      //@ assert (false ? false : false);\n" + 
				"   }\n" + 
				"   public void m44() {\n" + 
				"      //@ assert (false ? false : \n" +
				"                          (false ? false : true));\n" + 
				"   }\n" + 
				"   public void m45() {\n" + 
				"      //@ assert (false ? false : \n" +
				"                          (false ? false : false));\n" + 
				"   }\n" + 	
				"   public void m46() {\n" + 
				"      //@ assert 42 == 42;\n" + 
				"   }\n" + 
				"   public void m47() {\n" + 
				"      //@ assert 42 == 43;\n" + 
				"   }\n" + 
				"   public void m48() {\n" + 
				"      //@ assert 42 != 42;\n" + 
				"   }\n" + 
				"   public void m49() {\n" + 
				"      //@ assert 42 != 43;\n" + 
				"   }\n" + 
				"   public void m50() {\n" + 
				"      //@ assert 42 < 42;\n" + 
				"   }\n" + 
				"   public void m51() {\n" + 
				"      //@ assert 42 < 43;\n" + 
				"   }\n" + 
				"   public void m52() {\n" + 
				"      //@ assert 42 > 42;\n" + 
				"   }\n" + 
				"   public void m53() {\n" + 
				"      //@ assert 42 > 43;\n" + 
				"   }\n" + 
				"   public void m54() {\n" + 
				"      //@ assert 43 <= 42;\n" + 
				"   }\n" + 
				"   public void m55() {\n" + 
				"      //@ assert 42 <= 42;\n" + 
				"   }\n" + 
				"   public void m56() {\n" + 
				"      //@ assert 42 <= 43;\n" + 
				"   }\n" + 
				"   public void m57() {\n" + 
				"      //@ assert 42 >= 43;\n" + 
				"   }\n" + 
				"   public void m58() {\n" + 
				"      //@ assert 42 >= 42;\n" + 
				"   }\n" + 
				"   public void m59() {\n" + 
				"      //@ assert 43 >= 42;\n" + 
				"   }\n" + 
				"   public void m60() {\n" + 
				"      //@ assert (42 >= 42) == true;\n" + 
				"   }\n" + 
				"   public void m61() {\n" + 
				"      //@ assert (42 >= 42) == false;\n" + 
				"   }\n" + 
				"   public void m62() {\n" + 
				"      //@ assert (43 >= 42) == true;\n" + 
				"   }\n" + 
				"   public void m63() {\n" + 
				"      //@ assert (43 >= 42) == false;\n" + 
				"   }\n" + 
				"   public void m64() {\n" + 
				"      //@ assert 5 + 2 == 7;\n" + 
				"   }\n" + 
				"   public void m65() {\n" + 
				"      //@ assert 5 - 2 == 3;\n" + 
				"   }\n" + 
				"   public void m66() {\n" + 
				"      //@ assert 5 * 2 == 10;\n" + 
				"   }\n" + 
				"   public void m67() {\n" + 
				"      //@ assert 4 / 2 == 2;\n" + 
				"   }\n" + 
				"   public void m68() {\n" + 
				"      //@ assert 5 % 2 == 1;\n" + 
				"   }\n" + 
				"   public void m69() {\n" + 
				"      //@ assert 5 + 2 != 7;\n" + 
				"   }\n" + 
				"   public void m70() {\n" + 
				"      //@ assert 5 - 2 != 3;\n" + 
				"   }\n" + 
				"   public void m71() {\n" + 
				"      //@ assert 5 * 2 != 10;\n" + 
				"   }\n" + 
				"   public void m72() {\n" + 
				"      //@ assert 4 / 2 != 2;\n" + 
				"   }\n" + 
				"   public void m73() {\n" + 
				"      //@ assert 5 % 2 != 1;\n" + 
				"   }\n" + 		
				"   public void m74() {\n" + 
				"      //@ assert (5 == 3 + 2 ? 42 == 6 * 7 : 1 + 1 == 2);\n" + 
				"   }\n" + 
				"   public void m75() {\n" + 
				"      //@ assert (5 == 3 + 2 ? 42 > 6 * 7 : 1 + 1 == 2);\n" + 
				"   }\n" + 
				"   public void m76() {\n" + 
				"      //@ assert (5 == 3 + 3 ? 42 == 6 * 7 : 1 + 1 != 2);\n" + 
				"   }\n" + 
				"   public void m77() {\n" + 
				"      //@ assert (!true ? false : !true);\n" + 
				"   }\n" + 
				"   public void m78() {\n" + 
				"      //@ assert (false && false ? true : false && false);\n" + 
				"   }\n" + 
				"   public void m79() {\n" + 
				"      //@ assert (false || false ? true : false || false);\n" + 
				"   }\n" +	
				"   public void m80() {\n" +
				"      //@ assert (true ==> true);\n" + 
				"   }\n" + 
				"   public void m81() {\n" + 
				"      //@ assert (true ==> false);\n" + 
				"   }\n" + 
				"   public void m82() {\n" + 
				"      //@ assert (false ==> true);\n" + 
				"   }\n" + 
				"   public void m83() {\n" + 
				"      //@ assert (false ==> false);\n" + 
				"   }\n" + 	
				"   public void m84() {\n" +
				"      //@ assert (true <== true);\n" + 
				"   }\n" + 
				"   public void m85() {\n" + 
				"      //@ assert (true <== false);\n" + 
				"   }\n" + 
				"   public void m86() {\n" + 
				"      //@ assert (false <== true);\n" + 
				"   }\n" + 
				"   public void m87() {\n" + 
				"      //@ assert (false <== false);\n" + 
				"   }\n" + 		
				"   public void m88() {\n" +
				"      //@ assert (true <==> true);\n" + 
				"   }\n" + 
				"   public void m89() {\n" + 
				"      //@ assert (true <==> false);\n" + 
				"   }\n" + 
				"   public void m90() {\n" + 
				"      //@ assert (false <==> true);\n" + 
				"   }\n" + 
				"   public void m91() {\n" + 
				"      //@ assert (false <==> false);\n" + 
				"   }\n" + 	
				"   public void m92() {\n" +
				"      //@ assert (true <=!=> true);\n" + 
				"   }\n" + 
				"   public void m93() {\n" + 
				"      //@ assert (true <=!=> false);\n" + 
				"   }\n" + 
				"   public void m94() {\n" + 
				"      //@ assert (false <=!=> true);\n" + 
				"   }\n" + 
				"   public void m95() {\n" + 
				"      //@ assert (false <=!=> false);\n" + 
				"   }\n" + 	
				"   public void m96() {\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m97() {\n" + 
				"      //@ assert false;\n" + 
				"   }\n" +
				"   public void m98(boolean b) {\n" + 
				"      //@ assume b;\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 
				"   public void m99(boolean b) {\n" +
				"      //@ assume  b;\n" +
				"      //@ assert !b;\n" +
				"   }\n" +
				"   public void m100(int n) {\n" +
				"      //@ assume n==3;\n" +
				"      //@ assert n<4;\n" +
				"   }\n" +
				"   public void m101(int n) {\n" +
				"      //@ assume n==3;\n" +
				"      //@ assert n<0;\n" +
				"   }\n" +		
				"   public void m102() {\n" + 
				"      boolean b = true;\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 
				"   public void m103() {\n" +
				"      boolean b = true;\n" + 
				"      //@ assert !b;\n" +
				"   }\n" +
				"   public void m104() {\n" +
				"      int n=3;\n" +
				"      //@ assert n<4;\n" +
				"   }\n" +
				"   public void m105() {\n" +
				"      int n=3;\n" +
				"      //@ assert n<0;\n" +
				"   }\n" +
				"   public void m106() {\n" +
				"       { int n=3;\n" +
				"         //@ assert n==3;\n" +
				"       }\n" +
				"       { int n=4;\n" +
				"         //@ assert n!=3;\n" +
				"       }\n" +
				"   }\n" +	
				"   public void m107(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"   }\n" + 
				"   public void m108(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a <= 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"   }\n" + 
				"   public void m109(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a >= 0;\n" + 
				"      }\n" + 
				"   }\n" + 
				"   public void m110(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"   public void m111(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"   public void m112() {\n" + 
				"      if (true) {\n" + 
				"         //@ assert false;\n" + 
				"      } else {\n" +
				"         //@ assert true;\n" + 
				"      }\n" + 
				"      //@ assert true;\n" + 
				"   }\n" + 
				"   public void m113() {\n" + 
				"      if (true) {\n" + 
				"         //@ assert true;\n" + 
				"      } else {\n" +
				"         //@ assert true;\n" + 
				"      }\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m114(int i) {\n" + 
				"      int r;\n" + 
				"      if (i < 0) {\n" + 
				"         r = -i;\n" + 
				"      } else {\n" +
				"         r = i;\n" + 
				"      }\n" + 
				"      //@ assert r < 0;\n" + 
				"   }\n" + 
				"   public void m115(int i) {\n" + 
				"      int r;\n" + 
				"      if (i < 0) {\n" + 
				"         r = -i;\n" + 
				"      } else {\n" +
				"         r = i;\n" + 
				"      }\n" + 
				"      //@ assert r >= 0;\n" + 
				"   }\n" + 
				"   public void m116(int i) {\n" + 
				"      if (i < 0) {\n" + 
				"         i = -i;\n" + 
				"      }\n" + 
				"      //@ assert i < 0;\n" + 
				"   }\n" + 
				"   public void m117(int i) {\n" + 
				"      if (i < 0) {\n" + 
				"         i = -i;\n" + 
				"      }\n" + 
				"      //@ assert i >= 0; // 88\n" + 
				"   }\n" + 
				"   public void m118() {\n" + 
				"      if (true) {\n" + 
				"      	  //@ assert false;\n" + 
				"      }\n" + 
				"   }\n" +
				"   public void m119(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (++a > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m120(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if (a++ > 0) {\n" + 
				"         //@ assert a > 1;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 1;\n" + 
				"      }\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public void m121(int b) {\n" + 
				"      int a = 2 + b;\n" + 
				"      if ((a+=5) > 0) {\n" + 
				"         //@ assert a > 0;\n" + 
				"      } else {\n" +
				"         //@ assert a <= 0;\n" + 
				"      }\n" + 
				"      //@ assert false;\n" + 
				"   }\n" + 
				"   public static int m122(int a, int b) {\n" +
				"		if (b == 0)\n"+
				"          return a;\n" +
				"		else {\n"+
				"          return b;\n" +
				"       }\n" +
				"    }\n" +
				"   public void m123(boolean b) {\n" + 
				"      b = true;\n" + 
				"      //@ assert b;\n" + 
				"   }\n" + 
				"   public void m124(boolean b) {\n" + 
				"      b = true;\n" + 
				"      //@ assert !b;\n" + 
				"   }\n" + 
				"   public void m125(int a, int b) {\n" + 
				"      a = 3 + (b=2);\n" + 
				"      //@ assert a == 5 && b == 2;\n" + 
				"   }\n" + 
				"   public void m126(int a, int b) {\n" + 
				"      a = 3 + (b=2);\n" + 
				"      //@ assert a != 5 || b != 2;\n" + 
				"   }\n" + 
				"   public void m127(int a, int b) {\n" + 
				"      b = 1;\n" + 
				"      a = b + (b=2) + b + (b=3) + b;\n" + 
				"      //@ assert a == 11 && b == 3;\n" + 
				"   }\n" + 
				"   public void m128(int a, int b) {\n" + 
				"      b = 1;\n" + 
				"      a = b + (b=2) + b + (b=3) + b;\n" + 
				"      //@ assert a != 11 || b != 3;\n" + 
				"   }\n" + 
				"   public void m129(int a, int b) {\n" + 
				"      a = 1;\n" + 
				"      b = 2;\n" + 
				"      a = 3;\n" + 
				"      //@ assert a != 3 || b != 2;\n" + 
				"   }\n" + 
				"   public void m130(int a, int b) {\n" + 
				"      a = 1;\n" + 
				"      b = 2;\n" + 
				"      a += b;\n" + 
				"      //@ assert a != 3 || b != 2;\n" + 
				"   }\n" + 
				"   public void m131(int a, int b) {\n" + 
				"      a = 1;\n" + 
				"      b = 2;\n" + 
				"      a -= b;\n" + 
				"      //@ assert a != -1 || b != 2;\n" + 
				"   }\n" + 
				"   public void m132(int a, int b) {\n" + 
				"      a = 3;\n" + 
				"      b = 2;\n" + 
				"      a *= b;\n" + 
				"      //@ assert a != 6 || b != 2;\n" + 
				"   }\n" + 
				"   public void m133(int a, int b) {\n" + 
				"      a = 6;\n" + 
				"      b = 2;\n" + 
				"      a /= b;\n" + 
				"      //@ assert a != 3 || b != 2;\n" + 
				"   }\n" + 
				"   public void m134(int a, int b) {\n" + 
				"      a = 5;\n" + 
				"      b = 2;\n" + 
				"      a = b++;\n" + 
				"      //@ assert a != 2 || b != 3;\n" + 
				"   }\n" + 
				"   public void m135(int a, int b) {\n" + 
				"      a = 5;\n" + 
				"      b = 2;\n" + 
				"      a = ++b;\n" + 
				"      //@ assert a != 3 || b != 3;\n" + 
				"   }\n" + 
				"   public void m136(int a, int b) {\n" + 
				"      a = 5;\n" + 
				"      b = 2;\n" + 
				"      a = b--;\n" + 
				"      //@ assert a != 2 || b != 1;\n" + 
				"   }\n" + 
				"   public void m137(int a, int b) {\n" + 
				"      a = 5;\n" + 
				"      b = 2;\n" + 
				"      a = --b;\n" + 
				"      //@ assert a != 1 || b != 1;\n" + 
				"   }\n" +	
				"   //@ requires i138 > 10;\n" +
				"   //@ ensures \\result < -10;\n" +
				"   public static int m138(int i138) {\n" +
				"	   //@ return -i138;\n" +
				"	}\n" +
				"   //@ requires i139 < 10;\n" +
				"   //@ ensures \\result < -10;\n" +
				"   public static int m139(int i139) {\n" +
				"	   //@ return -i139;\n" +
				"	}\n" +
				"   //@ requires i140 > 0;\n" +
				"   //@ ensures \\result == i140 * i140 + 1;\n" +
				"   public static int sq_p140(int i140) {\n" +
				"	   return i140*i140 + 1;\n" +
				"	}\n" +
				"   public static void m141() {\n" +
				"	   //@ assert 26 == sq_p140(5);\n" +
				"	   int n = 5;\n" +
				"	   //@ assert 26 == sq_p140(n);\n" +
				"	}\n" +
				"   public static void m142() {\n" +
				"	   //@ assert 37 != sq_p140(6);\n" +
				"	   int n = 6;\n" +
				"	   //@ assert 37 != sq_p140(n);\n" +
				"	}\n" +
				"   //@ requires i143 > 0;\n" +
				"   //@ ensures \\result == i143 * i143;\n" +
				"   public static int sq143(int i143) {\n" +
				"	   return i143*i143;\n" +
				"	}\n" +
				"   //@ requires i144 > 0;\n" +
				"   //@ ensures \\result == i144 * sq143(i144);\n" +
				"   public static int cube144(int i144) {\n" +
				"	   return i144*i144*i144;\n" +
				"	}\n" +
				"   //@ requires i145 > 1;\n" +
				"   public static void m145(int i145) {\n" +
				"	   //@ assert cube144(i145) == i145 * i145 * i145;\n" +
				"	}\n" +
				"   //@ requires i146 > 1;\n" +
				"   public static void m146(int i146) {\n" +
				"	   //@ assert cube144(i146) == i146 * i146 + i146;\n" +
				"	}\n" +	
				"   //@ requires i147 > 0;\n" +
				"   //@ ensures \\result == i147 * i147;\n" +
				"   public static int sq147(int i147) {\n" +
				"	   return i147*i147;\n" +
				"	}\n" +	
				"   //@ requires i148 > 0;\n" +
				"   //@ ensures \\result == i148 * sq147(i148);\n" +
				"   public static int cube148(int i148) {\n" +
				"	   return i148*i148*i148;\n" +
				"	}\n" +
				"   //@ requires i149 > 0;\n" +
				"   //@ requires j149 > 0;\n" +
				"   //@ ensures \\result == sq147(i149) * sq147(j149);\n" +
				"   public static int sq_sq149(int i149, int j149) {\n" +
				"	   return i149*i149*j149*j149;\n" +
				"	}\n" +	
				"   public static void m150() {\n" +
				"	   //@ assert (\\forall int i, j; i > 0 && i==j; sq_sq149(i, j) == i * cube148(j));\n" +
				"	}\n" +	
				"   public static void m151(int i) {\n" +
				"	   int b = (++i < 0 ? -1 : (i*=2));\n" +
				"	   //@ assert (b == -1) ==> (i < 0);\n" +
				"	   //@ assert (b > 0) ==> (i >  0);\n" +
				"	}\n" +
				"   public static void m152(int i) {\n" +
				"	   int b = (++i - (i > 0 ? i+1 : i--) < 0 ? -1 : (i*=2));\n" +
				"	}\n" +
				"   public static void m153(int i) {\n" +
				"	   int b = (++i < 0 ? -1 - (i > 0 ? i+1 : i--) : (i*=2));\n" +
				"	}\n" +
				"   public static void m154(int i) {\n" +
				"	   int b = (++i < 0 ? -1 : (i*=2) - (i > 0 ? i+1 : i--));\n" +
				"	}\n" +
				"	//@ ensures \\result > 0 && \\result % 2 == 1;\n" +
				"	public int m155() {\n" +
				"		return 42;\n" +
				"	}\n" +	
				" //------QuantifierTests----156 TO ------------------\n" +
				"   public void m156() {\n" + 
				"      //@ assert (\\exists int i,j; 0 <= i & j < 10; i < j);\n" + 
				"      //@ assert (\\exists int i,j; j <= 5 & i > 10; i < j);\n" + 
				"      //@ assert (\\forall int i; 0 < i ; 0 <= i);\n" + 
				"      //@ assert (\\forall int i; 0 < i ; i <= 0);\n" + 
				"   }\n" +	
				"   public void m157() {\n" + 
				"      //@ assert (\\exists int i,j; 0 <= i && j < 10; i < j);\n" + 
				"      //@ assert (\\exists int i,j; j <= 5 && i > 10; i < j);\n" + 
				"   }\n" +
				"   public void m158(int i, int j) {\n" +
				"		/*@ assert ( i > j\n" +
				"		  @      ?  (\\forall int k ; i + k >  j + k )\n" +
				"		  @      :  (\\forall int k ; i + k <= j + k ));\n" +
				"		  @*/\n" +
				"	}\n" +
				"   public void m159() {\n" +
				"		//@ assert 5 == (\\sum int i ; 2 <= i && i <= 3; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 2 <= i && i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <  i && i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 2 <= i &  i <= 3; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 2 <= i &  i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <  i &  i <  4; i);\n" +
				"	}\n" +
				"   public void m160() {\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <= i && i <= 3; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <= i && i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 0 <  i && i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <= i &  i <= 3; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 1 <= i &  i <  4; i);\n" +
				"		//@ assert 5 == (\\sum int i ; 0 <  i &  i <  4; i);\n" +
				"	}\n" +
				"   public void m161() {\n" +
				"		//@ assert 6 == (\\product int i ; 2 <= i && i <= 3; i);\n" +
				"		//@ assert 6 == (\\product int i ; 2 <= i && i <  4; i);\n" +
				"		//@ assert 6 == (\\product int i ; 1 <  i && i <  4; i);\n" +
				"		//@ assert 6 == (\\product int i ; 2 <= i &  i <= 3; i);\n" +
				"		//@ assert 6 == (\\product int i ; 2 <= i &  i <  4; i);\n" +
				"		//@ assert 6 == (\\product int i ; 1 <  i &  i <  4; i);\n" +
				"	}\n" +
				"   public void m162() {\n" +
				"		//@ assert 5 == (\\product int i ; 1 <= i && i <= 3; i);\n" +
				"		//@ assert 5 == (\\product int i ; 1 <= i && i <  4; i);\n" +
				"		//@ assert 5 == (\\product int i ; 0 <  i && i <  4; i);\n" +
				"		//@ assert 5 == (\\product int i ; 1 <= i &  i <= 3; i);\n" +
				"		//@ assert 5 == (\\product int i ; 1 <= i &  i <  4; i);\n" +
				"		//@ assert 5 == (\\product int i ; 0 <  i &  i <  4; i);\n" +
				"	}\n" +		
				"   public void m163() {\n" +
				"		//@ assert 1 == (\\num_of int i ; 2 <= i && i <= 3; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 2 <= i && i <  4; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 1 <  i && i <  4; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 2 <= i &  i <= 3; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 2 <= i &  i <  4; i % 2 == 0);\n" +
				"		//@ assert 1 == (\\num_of int i ; 1 <  i &  i <  4; i % 2 == 0);\n" +
				"	}\n" +
				"   public void m164() {\n" +
				"		//@ assert 2 == (\\num_of int i ; 2 <= i && i <= 3; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 2 <= i && i <  4; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 1 <  i && i <  4; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 2 <= i &  i <= 3; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 2 <= i &  i <  4; i % 2 == 0);\n" +
				"		//@ assert 2 == (\\num_of int i ; 1 <  i &  i <  4; i % 2 == 0);\n" +
				"	}\n" +
				"   //@ requires b166 >= 0;\n" +
				"   //@ requires a166 > 0;\n" +
				"   //@ ensures  \\result == (b166 % a166 == 0);\n" +
				"   public static boolean m166_divides(int a166, int b166) {\n" +
				"      return (b166 - (b166/a166)*a166) == 0;\n" +
				"   }\n" +
				"	\n" +
				"	//@ requires 0 < c166;\n" +
				"   //@ requires 0 < a166;\n" +
				"   //@ requires 0 < i166;\n" +
				"   //@ requires c166 < a166;\n" +
				"   //@ requires c166 <= a166;\n" +
				"   //@ requires 0 <= a166-i166+1;\n" +
				"   public static void m166(int c166, int a166, int i166) {\n" +
				"      /*@ assume (\\forall int d;\n" +
				"        @                 (0 < d) & (d <= i166);\n" +
				"        @                 m166_divides(d, a166)\n" +
				"        @                    ==> d <= c166);\n" +
				"        @*/\n" +
				"      /*@ assert (\\forall int e;\n" +
				"        @                 (0 < e) & (e <= i166);\n" +
				"        @                 m166_divides(e, a166)\n" +
				"        @                    ==> e <= c166);\n" +
				"        @*/\n" +
				"   }\n" +	
				
				"   public void n() {\n" + 
				"      //@ assert false;\n" + 
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result == 0;\n" +
				"   public int n1(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result != 0;\n" +
				"   public int n2(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result != 0;\n" +
				"   public int n3(int x)\n" +
				"   {\n" +
				"      //@ assert false;\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-2;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result == 0;\n" +
				"   public int n1a(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result != 0;\n" +
				"   public int n2a(int x)\n" +
				"   {\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-1;\n" +
				"      return x;\n" +
				"   }\n" +
				"   //@ requires 100 <= x;\n" +
				"   //@ ensures  \\result != 0;\n" +
				"   public int n3b(int x)\n" +
				"   {\n" +
				"      //@ assert false;\n" +
				"      //@ loop_invariant 0 <= x;\n" +
				"      while (0 < x)\n" +
				"            x = x-2;\n" +
				"      return x;\n" +
				"   }\n" +
				"   public void nd(boolean b, boolean p) {\n" +
				"      while (b) {\n" +
				"            if (p) {\n" +
				"               break;\n" +
				"            }\n" +
				"      }\n" +
				"   }\n" +
				"  //@ requires i;" +
				"  public void n_break_2d(boolean b, boolean i) {\n" +
				"      if (b) {\n" +
				"          //@ loop_invariant i;\n" +
				"          while (b) {\n" +
				"              //@ assert b & i;\n" +
				"              break;\n" +
				"          }\n" +
				"      }\n" +
				"  }\n" +
				"  //@ requires i & j;" +
				"  //@ ensures  b & i & j;" +
				"  public void n_break_3d(boolean b, boolean i, boolean j) {\n" +
				"      if (b) {\n" +
				"          //@ loop_invariant i;\n" +
				"          while (b) {\n" +
				"              //@ assert b & i & j;\n" +
				"              break;\n" +
				"          }\n" +
				"          //@ assert b & i & j; // we know b\n" +
				"      }\n" +
				"      //@ assert b & i & j; // we don't know b\n" +
				"  }\n" +
				"  //@ requires i & j;" +
				"  public void n_break_4d(boolean b, boolean i, boolean j) {\n" +
				"      if (b) {\n" +
				"          //@ loop_invariant i;\n" +
				"          while (b) {\n" +
				"              //@ assert b & i & j;\n" +
				"              break;\n" +
				"          }\n" +
				"      }\n" +
				"  }\n" +
				"  //@ requires 100 <= y;\n" +
				"  public static int n4d(int y) {\n" +
				"    //@ loop_invariant 0 <= y;\n" +
				"    while (0 < y) {\n" +
				"          //@ assert true;\n" +
				"          if (y<0) {\n" +
				"             //@ assert true;\n" +
				"             break;\n" +
				"          }\n" +
				"          y = y - 1;\n" +
				"          //@ assert 0 <= y;\n" +
				"    }\n" +
				"    //@ assert false; // here\n" +
				"    return y;\n" +
				"  }\n" +
				"  //@ requires i & j;\n" +
				"  //@ ensures  i & j & b;\n" +
				"  public void n_break_1d(boolean b, boolean i, boolean j) {\n" +
				"      //@ loop_invariant i;\n" +
				"      while (b) {\n" +
				"          //@ assert b;\n" +
				"          //@ assert i;\n" +
				"          //@ assert j;\n" +
				"          break;\n" +
				"      }\n" +
				"  }\n" +
				"	//@ requires j;\n" +
				"   public static void n_while_1e(boolean b, boolean j) {\n" +
				"		if (b) {\n" +
				"			//@ assert b & j;\n" +
				"			while (true) {\n" +
				"				j = false;\n" +
				"				break;\n" +
				"			}\n" +
				"			//@ assert b & !j;\n" +
				"		} else {\n" +
				"			//@ assert !b & j;\n" +
				"		}\n" +
				"		//@ assert j;\n" +
				"	}\n" +
				"	//@ requires j;\n" +
				"   public static void n_while_2e(boolean b, boolean j) {\n" +
				"		if (b) {\n" +
				"			//@ assert b & j;\n" +
				"			while (true) {\n" +
				"				j = false;\n" +
				"				break;\n" +
				"			}\n" +
				"			//@ assert b & !j;\n" +
				"		} else {\n" +
				"			//@ assert !b & j;\n" +
				"		}\n" +
				"		//@ assert (b & !j) | (!b & j);\n" +
				"	}\n" +
				"   public static void n0f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 0;\n" +
				"		while (i > 0) {\n" +
				"             i--;\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"	}\n" +
				"   public static void n1f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i > 0;\n" +
				"		while (--i > 0) {\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"	}\n" +
				"   public static void n2f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 3;\n" +
				"		while (i-- > 3) {\n" +
				"		}\n" +
				"		//@ assert i == 2;\n" +
				"	}\n" +
				"   public static void n3f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 0;\n" +
				"		while (--i > 0) {\n" +
				"		}\n" +
				"		//@ assert i == 4;\n" +
				"	}\n" +
				"   public static void n4f() {\n" +
				"		int i = 10;\n" +
				"		//@ loop_invariant i >= 0;\n" +
				"		while (i-- > 1) {\n" +
				"		}\n" +
				"		//@ assert i == 1;\n" +
				"	}\n" +
				"   public static void n1g() {\n" +
				"		int a = 10;\n" +
				"		//@ decreases a;\n" +
				"		while (a > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n2g() {\n" +
				"		int b = 10;\n" +
				"		//@ decreases b;\n" +
				"		while (b > 0) {\n" +
				"             b--;\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n3g() {\n" +
				"		int c = 10;\n" +
				"		//@ decreases c;\n" +
				"		while (c > 0) {\n" +
				"             c++;\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n4g() {\n" +
				"		int d = 10;\n" +
				"		//@ decreases d;\n" +
				"		while (--d > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n5g() {\n" +
				"		int e = 10;\n" +
				"		//@ decreases e;\n" +
				"		while (++e > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n6g() {\n" +
				"		int f = 10;\n" +
				"		//@ decreases f;\n" +
				"		while (f-- > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n7g() {\n" +
				"		int g = 10;\n" +
				"		//@ decreases g;\n" +
				"		while (g++ > 0) {\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n8g(boolean b) {\n" +
				"		int h = 10;\n" +
				"		//@ decreases h;\n" +
				"		while (h > 0) {\n" +
				"             if (b) {\n" +
				"                h--;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n9g() {\n" +
				"		int i = 10;\n" +
				"		boolean b = true;\n" +
				"		//@ decreases i;\n" +
				"		while (i > 0) {\n" +
				"             if (b) {\n" +
				"                i--;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n1h(boolean b) {\n" +
				"		int i = 10;\n" +
				"		//@ decreases i;\n" +
				"		while (i > 0) {\n" +
				"             if (b) {\n" +
				"                i--;\n" +
				"                continue;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"   public static void n2h() {\n" +
				"		int j = 10;\n" +
				"		boolean c = (j / 5 == 2);\n" +
				"		//@ decreases j;\n" +
				"		while (j > 0) {\n" +
				"             if (c) {\n" +
				"                j--;\n" +
				"                continue;\n" +
				"		      }\n" +
				"		}\n" +
				"	}\n" +
				"	//@ requires b >= 0;\n" +
				"	//@ ensures \\result == a + b;\n" +
				"	public int nsum1(final int a, final int b) {\n" +
				"		int sum = a;\n" +
				"		int i = b;\n" +
				"		//@ maintaining sum == a + b - i;\n" +
				"		//@ maintaining i >= 0;\n" +
				"		//@ decreasing i;\n" +
				"		while (i != 0) {\n" +
				"			sum++;\n" +
				"			i -= 1;\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"		return sum;\n" +
				"	}\n" + 
				"	//@ requires b >= 0;\n" +
				"	//@ ensures \\result == a + b;\n" +
				"	public int nsum2(final int a, final int b) {\n" +
				"		int sum = a;\n" +
				"		int i = b;\n" +
				"		//@ maintaining sum == a + b - i;\n" +
				"		//@ decreasing i;\n" +
				"		while (i != 0) {\n" +
				"			sum++;\n" +
				"			i -= 1;\n" +
				"		}\n" +
				"		//@ assert i == 0;\n" +
				"		return sum;\n" +
				"	}\n" + 
				"	//@ requires b >= 0;\n" +
				"	//@ ensures \\result == a + b + 1;\n" +
				"	public int nsum1b(final int a, final int b) {\n" +
				"		int sum = a;\n" +
				"		int i = b;\n" +
				"		//@ maintaining sum == a + b - i;\n" +
				"		//@ maintaining i+1 >= 0;\n" +
				"		//@ decreasing i+1;\n" +
				"		while (i-- >= 0) {\n" +
				"			sum++;\n" +
				"		}\n" +
				"		//@ assert i == -2;\n" +
				"		return sum;\n" +
				"	}\n" + 
				"	//@ requires b >= 0;\n" +
				"	public void noSideEffects(int b) {\n" +
				"		int i = b;\n" +
				"		//@ maintaining i+1 >= 0;\n" +
				"		//@ decreasing i+1;\n" +
				"		while (i >= 0) {\n" +
				"		      i--;\n" +
				"		}\n" +
				"		//@ assert i == -1;\n" +
				"	}\n" + 
				"	//@ requires b >= 0;\n" +
				"	public void nsum1c(final int b) {\n" +
				"		int i = b;\n" +
				"		//@ maintaining i+1 >= 0;\n" +
				"		//@ decreasing i+1;\n" +
				"		while (i-- >= 0) {\n" +
				"		}\n" +
				"		//@ assert i == -2;\n" +
				"	}\n" + 
				"	public int nm1i() {\n" +
				"		int m=10;\n" +
				"		//@ maintaining m >= 0;\n" +
				"		while (m > 0) {\n" +
				"		      m = m - 1;\n" +
				"		}\n" +
				"		//@ assert m == 0;\n" +
				"		return m;\n" +
				"	}\n" +
				"	public int nm2i() {\n" +
				"		int m=10;\n" +
				"		//@ maintaining m >= 0;\n" +
				"		while (m-- > 1) {\n" +
				"		}\n" +
				"		//@ assert m == 0;\n" +
				"		return m;\n" +
				"	}\n" +
				"	public int nm3i() {\n" +
				"		int m=10;\n" +
				"		//@ maintaining m >= 0;\n" +
				"		while (m-- > 2) {\n" +
				"		}\n" +
				"		//@ assert m == 0;\n" +
				"		//@ assert false;\n" +
				"		return m;\n" +
				"	}\n" +
				"	//@ requires j;\n" +
				"   public static void m1j(boolean b, boolean j) {\n" +
				"      if (b) {\n" +
				"         //@ assert b & j;\n" +
				"         //@ loop_invariant b;\n" +
				"         while (true) {\n" +
				"            j = false;\n" +
				"         	break;\n" +
				"         }\n" +
				"         //@ assert !j;\n" +
				"         //@ assert  b;\n" +
				"      }\n" +
				"   }\n" +
				"	//@ requires j;\n" +
				"   public static void nm1k(boolean b, boolean j) {\n" +
				"      if (b) {\n" +
				"         //@ assert b & j;\n" +
				"         //@ loop_invariant b;\n" +
				"         while (true) {\n" +
				"            j = false;\n" +
				"         	break;\n" +
				"         }\n" +
				"         //@ assert !j;\n" +
				"      }\n" +
				"      //@ assert b;\n" +
				"   }\n" +
				"   //@ requires j;\n" +
				"   public static void n2l(boolean b, boolean j) {\n" +
				"      if (b) {\n" +
				"         //@ assert b & j;\n" +
				"         if (true) {\n" +
				"            j = false;\n" +
				"         } else {\n" +
				"          b = true;\n" + // redundant info to change incarnation
				"         }\n" +
				"      //@ assert !j;\n" +
				"      //@ assert  b;\n" +
				"      }\n" +
				"      //@ assert b;\n" +
				"   }\n" +
				"	//@ requires y >= 0 && x >= 0;\n" +
				"	//@ ensures  \\result == x + y * y;\n" +
				"	public int n_22_comp(int x, int y) {\n" +
				"		int z = x;\n" +
				"		int w = y;\n" +
				"\n" +
				"		//@ assert (y*w) + z == x + y * y;\n" +
				"\n" +
				"		//@ maintaining z == x + y * y - w*y;\n" +
				"		//@ decreasing w;\n" +
				"		while (w > 0) {\n" +
				"			z += y;\n" +
				"			w--;\n" +
				"			//@ assert (y*w) + z == x + y * y;\n" +
				"		}\n" +
				"		return z;\n" +
				"	}\n" +
				"	//@ requires y > 0;\n" +
				"	//@ ensures  \\result == x - y;\n" +
				"	public int n_23_diff(int x, int y) {\n" +
				"		int z = x;\n" +
				"		int w = y;\n" +
				"		//@ maintaining x -y == z - w;\n" +
				"		//@ maintaining w >= 0;\n" +
				"		while (w > 0) {\n" +
				"			z--;\n" +
				"			w--;\n" +
				"		}\n" +
				"		return z;\n" +
				"	}\n" +
				"	//@ requires x >= 0 && y >= 0;\n" +
				"	//@ ensures  \\result == x * y;\n" +
				"	public int n_24_times(int x, int y) {\n" +
				"		int z = 0;\n" +
				"		int w = y;\n" +
				"		//@ assert w >= 0;\n" +
				"		//@ assert z == x*y - x*w;\n" +
				"\n" +
				"		//@ maintaining w >= 0;\n" +
				"		//@ maintaining z == x*y - x*w;\n" +
				"		while (w > 0) {\n" +
				"			z += x;\n" +
				"			w--;\n" +
				"		    //@ assert w >= 0;\n" +
				"		    //@ assert z == x*y - x*w;\n" +
				"		}\n" +
				"		//@ assert w >= 0;\n" +
				"		return z;\n" +
				"	}\n" +
				"	//@ requires x >= 0 && y > 0;\n" +
				"	//@ ensures  \\result == x * y * y;\n" +
				"	public int n_24_power(int x, int y) {\n" +
				"		int z = 0;\n" +
				"		int w = y;\n" +
				"		//@ assert z+(x*w) == x*y;\n" +
				"\n" +
				"		//@ maintaining w >= 0;\n" +
				"		//@ maintaining z+(x*w) == x*y;\n" +
				"		while (w > 0) {\n" +
				"			z += x;\n" +
				"			w--;\n" +
				"			//@ assert z+(x*w) == x*y;\n" +
				"		}\n" +
				"		w = y-1;\n" +
				"		int u = z;\n" +
				"\n" +
				"		//@ assert z+(x*y*w) == x*y*y;\n" +
				"\n" +
				"		//@ maintaining w >= 0;\n" +
				"		//@ maintaining z+(x*y*w) == x*y*y;\n" +
				"		while (w > 0) {\n" +
				"			z += u;\n" +
				"			w--;\n" +
				"			//@ assert z+(x*y*w) == x*y*y;\n" +
				"		}\n" +
				"		return z;\n" +
				"	}\n" +
				"	//@ requires x > 0;\n" +
				"	//@ ensures  \\result == x * x * x;\n" +
				"	public int n_25_cube(int x) {\n" +
				"		int a = 1;\n" +
				"		int b = 0;\n" +
				"		int c = x;\n" +
				"		int z = 0;\n" +
				"		//@ maintaining a == 3*(x-c) + 1;\n" +
				"		//@ maintaining b == 3*(x-c)*(x-c);\n" +
				"		//@ maintaining z == (x-c)*(x-c)*(x-c);\n" +
				"		//@ decreasing c;\n" +
				"		while (c > 0) {\n" +
				"			z += a + b;\n" +
				"			b += 2*a + 1;\n" +
				"			a += 3;\n" +
				"			c--;\n" +
				"		}\n" +
				"		//@ assert z == x * x * x;\n" +
				"		return z;\n" +
				"	}\n" +
				"   public void n6m(int i) {\n" +
				"      int c = 5;\n" +
				"      int factorial = c;\n" +
				"      while (--c > 1)\n" +
				"            factorial *= c;\n" +
				"      //@ assert false;\n" +
				"   }\n" +
				"   //@ requires b >= 0;\n" +
				"   //@ ensures  \\result == a + b;\n" +
				"   public int sum1c2a(final int a, final int b) {\n" +
				"      int sum = a;\n" +
				"      int i = b;\n" +
				"      //@ maintaining sum == a + b - i;\n" +
				"      //@ maintaining i >= 0;\n" +
				"      //@ decreasing i+1;\n" +
				"      while (true) {\n" +
				"         //@ assert i >= 0;\n" +
				"         int var = i;\n" +
				"         if (!(i > 0)) {\n" +
				"            //@ assert i == 0;\n" +
				"            break;\n" +
				"         }\n" +
				"         sum++;\n" +
				"         i--;\n" +
				"         //@ assert i < var;\n" +
				"         //@ assert sum == a + b - i;\n" +
				"      }\n" +
				"      //@ assert i == 0;\n" +
				"      //@ assert sum == a + b - i;\n" +
				"      //@ assert sum == a + b;\n" +
				"      return sum;\n" +
				"   }\n" +
				"   public void countDownWithSideEffect2o() {\n" +
				"	   int i = 10;\n" +
				"	   //@ assert i  >= 0;\n" +
				"	   //@ maintaining i  >= 0;\n" +
				"	   //@ decreasing i;\n" +
				"	   while (0 < --i) {\n" +
				"	   }\n" +
				"	   //@ assert i >= 0;\n" +
				"	   //@ assert i == 0;\n" +
				"   }\n" +
				"}"
				

		},
				"----------\n" +
				"1. ERROR in tests\\esc\\X.java (at line 4)\n" +
				"	//@ requires n.length >= 4;\n" +
				"	             ^^^^^^^^^^^^^\n" +
				"Possible assertion failure (Precondition).\n" +
				"----------\n"
		); 
	}


}
