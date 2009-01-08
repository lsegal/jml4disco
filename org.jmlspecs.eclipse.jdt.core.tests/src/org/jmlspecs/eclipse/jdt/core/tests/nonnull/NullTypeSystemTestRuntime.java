package org.jmlspecs.eclipse.jdt.core.tests.nonnull;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class NullTypeSystemTestRuntime extends AbstractRegressionTest {

	public NullTypeSystemTestRuntime(String name) { 
	    super(name);
	}

	// Augment problem detection settings
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
	    Map<String, String> options = super.getCompilerOptions();

	    options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
	    options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NULLABLE);
	    options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.ENABLED);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.IGNORE);
		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_SpecPath, NullTypeSystemTestCompiler.getSpecPath());
	    return options;
	}

	public void _test_0001_nn_assignment() {
		this.runConformTest( new String[] {
				"Assignment.java",
				"public class Assignment {"+
                "	public Assignment() {/**/}\n" +
                "\n" +
                "	private void single(/*@ non_null */ Object[] paNon, /*@ nullable */ Object[] paAble) {\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			paNon = paAble;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 21\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment single 1\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "   }\n" +
                "\n" +
                "	public static void main(String[] args) {\n" +
                "		Assignment o = new Assignment();\n" +
                "		o.single(new Object[] {\"hello\"}, null); //$NON-NLS-1$\n" +
                "	}\n" +
                "\n" +
                "	public static void fail(String msg) {\n" +
                "		System.out.println(\"failure: \"+msg); //$NON-NLS-1$\n" +
                "	}\n" +
                "	public static void success() {\n" +
                "		System.out.println(\"success!\"); //$NON-NLS-1$\n" +
                "	}\n" +
                "}\n"
			   },
                "");
	}
    public void _test_0024_nn_assignment_1() {
		this.runConformTest(
			new String[] {
				"nn_assignment_1.java",
                "\n" +
                "\n" +
                "public class nn_assignment_1 {\n" +
                "\n" +
                "	/*@ non_null */ nn_assignment_1 non  = this;\n" +
                "	/*@ nullable */ nn_assignment_1 able = null;\n" +
                "\n" +
                "	/*@ non_null */ Object[] aNon  = new String[] { \"hello\" }; //$NON-NLS-1$\n" +
                "	/*@ nullable */ Object[] aAble = new String[] { null };\n" +
                "\n" +
                "	private void array(/*@ non_null */ Object[] paNon, /*@ nullable */ Object[] paAble) {\n" +
                "		/*@ non_null */ Object[] laNon  = new String[] { \"hello\" }; //$NON-NLS-1$\n" +
                "		/*@ nullable */ Object[] laAble = new String[] { null };\n" +
                "		\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			paNon[0] = paAble[0];\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 1\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment array 1\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			paAble[0] = paNon[0];\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 2\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment array 2\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			laNon[0] = laAble[0];\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 3\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment array 3\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			laAble[0] = laNon[0];\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 4\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment array 4\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			aNon[0] = aAble[0];\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 5\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment array 5\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			aAble[0] = aNon[0];\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 6\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment array 6\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "	}\n" +
                "\n" +
                "	private void single(/*@ non_null */ Object[] paNon, /*@ nullable */ Object[] paAble) {\n" +
                "		/*@ non_null */ Object[] laNon  = new String[] { \"hello\" }; //$NON-NLS-1$\n" +
                "		/*@ nullable */ Object[] laAble = null;\n" +
                "		\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			paNon = paAble;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 21\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment single 1\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			paAble = paNon;\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 22\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment single 2\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			laNon = laAble;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught good - 23\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment single 3\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			laAble = laNon;\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 24\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment single 4\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			non = able;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 25\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment single 5\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			able = non;\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 26\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment single 6\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "	}\n" +
                "\n" +
                "	private void qualified(/*@ non_null */ nn_assignment_1 pNon, /*@ nullable */ nn_assignment_1 pAble) {\n" +
                "		/*@ non_null */ nn_assignment_1 lNon  = new nn_assignment_1();\n" +
                "		/*@ nullable */ nn_assignment_1 lAble = null;\n" +
                "		\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			pNon.non = pNon.able;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 31\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment qualified 1\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			pNon.able = pNon.non;\n" +
                "			pNon.able = null;\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 32\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment qualified 2\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			lNon.non = lNon.able;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 33\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment qualified 3\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			lNon.able = lNon.non;\n" +
                "			lNon.able = null;\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 34\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment qualified 4\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "\n" +
                "		failed = true;\n" +
                "		non.able = null;\n" +
                "		try {\n" +
                "\n" +
                "			non.non = non.able;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 35\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment qualified 5\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "\n" +
                "		\n" +
                "		failed = true;\n" +
                "		non.able = null;\n" +
                "		try {\n" +
                "			non.able = non.non;\n" +
                "			non.able = null;\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 36\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment qualified 6\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "\n" +
                "		failed = true;\n" +
                "		this.able = null;\n" +
                "		try {\n" +
                "			this.non = this.able;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			//System.out.println(\"caught good - 37\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment qualified 7\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "		\n" +
                "		failed = true;\n" +
                "		this.able = null;\n" +
                "		try {\n" +
                "			this.able = this.non;\n" +
                "			this.able = null;\n" +
                "			failed = false;\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad - 38\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"assignment qualified 8\"); //$NON-NLS-1$\n" +
                "		else success();\n" +
                "	}\n" +
                "\n" +
                "	public nn_assignment_1() {/**/}\n" +
                "\n" +
                "	public static void main(String[] args) {\n" +
                "		nn_assignment_1 o = new nn_assignment_1();\n" +
                "\n" +
                "		o.array(new Object[] {\"hello\"}, new Object[] {null}); //$NON-NLS-1$\n" +
                "		o.single(new Object[] {\"hello\"}, null); //$NON-NLS-1$\n" +
                "		o.qualified(new nn_assignment_1(), null);\n" +
                "	}\n" +
                "\n" +
                "	public static void fail(String msg) {\n" +
                "		System.out.println(\"failure: \"+msg); //$NON-NLS-1$\n" +
                "	}\n" +
                "	public static void success() {\n" +
                "		System.out.println(\"success!\"); //$NON-NLS-1$\n" +
                "	}\n" +
                "}\n" 
			},
			    "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+
			    "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+
			    "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+
			    "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+
			    "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+ "success!\n"+
			    "success!\n"+ "success!\n"
			);
    }
    public void _test_0031_nn_field() {
		this.runNegativeTest(
			new String[] {
				"nn_field.java",
                "\n" +
                "\n" +
                "public class nn_field {\n" +
                "\n" +
                "	public static void main(String[] args) {\n" +
                "\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			nn_field_init_1 o = new nn_field_init_1();\n" +
                "			failed = false;\n" +
                "		} catch (Exception npe) {\n" +
                "			System.out.println(\"caught bad - field 1\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"field 1\"); //$NON-NLS-1$\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			nn_field_init_2 o = new nn_field_init_2();\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught good - field 2\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"field 2\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			nn_field_init_3 o = new nn_field_init_3();\n" +
                "			failed = false;\n" +
                "		} catch (Exception npe) {\n" +
                "			System.out.println(\"caught bad - field 3\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"field 3\"); //$NON-NLS-1$\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			nn_field_init_4 o = new nn_field_init_4();\n" +
                "		} catch (ExceptionInInitializerError npe) {\n" +
                "			System.out.println(\"caught good - field 4\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"field 4\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			nn_field_init_5 o = new nn_field_init_5();\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught good - field 5\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"field 5\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			nn_field_init_6 o = new nn_field_init_6();\n" +
                "		} catch (ExceptionInInitializerError npe) {\n" +
                "			System.out.println(\"caught good - field 6\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"field 6\"); //$NON-NLS-1$\n" +
                "\n" +
                "	}\n" +
                "\n" +
                "	public static void fail(String msg) {\n" +
                "		System.out.println(\"failure: \"+msg); //$NON-NLS-1$\n" +
                "	}\n" +
                "}\n" 
			},
			"");
    }
    public void _test_0032_nn_local_1() {
		this.runNegativeTest(
			new String[] {
				"nn_local_1.java",
                "\n" +
                "\n" +
                "public class nn_local_1 {\n" +
                "\n" +
                "	static int i = 3;\n" +
                "	static /*@ nullable */ String s = \"\"; //$NON-NLS-1$\n" +
                "\n" +
                "	public static void main(String[] args) {\n" +
                "\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			/*@ non_null */ Object non = \"\"+i; //$NON-NLS-1$\n" +
                "			/*@ nullable */ Object able = null;\n" +
                "			able = non;\n" +
                "			i += non.hashCode() + able.hashCode();\n" +
                "			failed = false;\n" +
                "		} catch (Exception npe) {\n" +
                "			System.out.println(\"caught bad - local 1\"); //$NON-NLS-1$\n" +
                "		}\n" +
                "		if (failed) fail(\"local 1\"); //$NON-NLS-1$\n" +
                "		\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			/*@ non_null */ Object non  = null;\n" +
                "			s = \"\"+non; //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught good - local 2\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"local 2\"); //$NON-NLS-1$\n" +
                "	}\n" +
                "\n" +
                "	public static void fail(String msg) {\n" +
                "		System.out.println(\"failure: \"+msg); //$NON-NLS-1$\n" +
                "	}\n" +
                "}\n" 
			},
			"");
    }
    public void test_0033_nn_param_1() {
		this.runConformTest(
			new String[] {
				"nn_param_1.java",
                "\n" +
                "\n" +
                "public class nn_param_1 {\n" +
                "\n" +
                "	public nn_param_1() {/**/}\n" +
                "\n" +
                "	public void m0(/*@ nullable */ String s1, /*@ nullable */ String s2) { /**/ }\n" +
                "	public void m1(/*@ non_null */ String s1, /*@ nullable */ String s2) { /**/ }\n" +
                "	public void m2(/*@ nullable */ String s1, /*@ non_null */ String s2) { /**/ }\n" +
                "\n" +
                "	public static void main(String[] args) {\n" +
                "       int caughtGood = 0;" +
                "		nn_param_1 o = new nn_param_1();\n" +
                "\n" +
                "		o.m0(null, null);\n" +
                "\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			o.m1(null, \"hello\"); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			caughtGood++;\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			o.m1(\"hello\", null); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 2\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			o.m2(\"hello\", null); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			caughtGood++;\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			o.m2(null, \"hello\"); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 2\"); //$NON-NLS-1$\n" +
                "       System.out.println(\"caughtGood == \"+caughtGood);//$NON-NLS-1$\n" +
                "\n" +
                "	}\n" +
                "\n" +
                "	public static void fail(String msg) {\n" +
                "		System.out.println(\"failure: \"+msg); //$NON-NLS-1$\n" +
                "	}\n" +
                "}\n" 
			},
                "caughtGood == 2" 
        );
    }
    public void test_0033b_nn_param_1_cons() {
		this.runConformTest(
			new String[] {
				"nn_param_1_cons.java",
                "\n" +
                "\n" +
                "public class nn_param_1_cons {\n" +
                "\n" +
                "	public nn_param_1_cons(/*@ nullable */ String s1, /*@ nullable */ String s2, int i) { /**/ }\n" +
                "	public nn_param_1_cons(/*@ non_null */ String s1, /*@ nullable */ String s2, boolean b) { /**/ }\n" +
                "	public nn_param_1_cons(/*@ nullable */ String s1, /*@ non_null */ String s2, Object o) { /**/ }\n" +
                "\n" +
                "	public static void main(String[] args) {\n" +
                "       int caughtGood = 0;\n" +
                "		nn_param_1_cons o;\n" +
                "\n" +
                "		o = new nn_param_1_cons(null, null, 1);\n" +
                "\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			o = new nn_param_1_cons(null, \"hello\", true); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			caughtGood++;\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			o = new nn_param_1_cons(\"hello\", null, true); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 2\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			o = new nn_param_1_cons(\"hello\", null, \"\"); //$NON-NLS-1$ //$NON-NLS-2$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			caughtGood++;\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			o = new nn_param_1_cons(null, \"hello\", \"\"); //$NON-NLS-1$ //$NON-NLS-2$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 2\"); //$NON-NLS-1$\n" +
                "       System.out.println(\"caughtGood == \"+caughtGood);//$NON-NLS-1$\n" +
                "\n" +
                "	}\n" +
                "\n" +
                "	public static void fail(String msg) {\n" +
                "		System.out.println(\"failure: \"+msg); //$NON-NLS-1$\n" +
                "	}\n" +
                "}\n" 
			},
                "caughtGood == 2" 
        );
    }
    public void _test_0034_nn_param_2() {
		this.runConformTest(
			new String[] {
				"nn_param_2.java",
                "\n" +
                "\n" +
                "public class nn_param_2 {\n" +
                "	public void m0(/*@ nullable */ String s1, /*@ nullable */ String s2) { /**/ }\n" +
                "	public void m1(/*@ non_null */ String s1, /*@ nullable */ String s2) { /**/ }\n" +
                "	public void m2(/*@ nullable */ String s1, /*@ non_null */ String s2) { /**/ }\n" +
                "\n" +
                "	public static void main(String[] args) {\n" +
                "		nn_param_2 o = new nn_param_2();\n" +
                "\n" +
                "		o.m0(null, null);\n" +
                "\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			o.m1(null, \"hello\"); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught good\"); //$NON-NLS-1$\n" +
                "			npe.printStackTrace();\n" +
                "			System.out.println();\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			o.m1(\"hello\", null); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad\"); //$NON-NLS-1$\n" +
                "			npe.printStackTrace();\n" +
                "			System.out.println();\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 2\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = true;\n" +
                "		try {\n" +
                "			o.m2(\"hello\", null); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught good\"); //$NON-NLS-1$\n" +
                "			npe.printStackTrace();\n" +
                "			System.out.println();\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			o.m2(null, \"hello\"); //$NON-NLS-1$\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			failed = true;\n" +
                "			System.out.println(\"caught bad\"); //$NON-NLS-1$\n" +
                "			npe.printStackTrace();\n" +
                "			System.out.println();\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 2\"); //$NON-NLS-1$\n" +
                "\n" +
                "	}\n" +
                "\n" +
                "	public static void fail(String msg) {\n" +
                "		System.out.println(\"failure: \"+msg); //$NON-NLS-1$\n" +
                "	}\n" +
                "}\n" 
			},
			"");
    }
    public void _test_0035_nn_return_1() {
		this.runNegativeTest(
			new String[] {
				"nn_return_1.java",
                "\n" +
                "\n" +
                "class nn_return_1 {\n" +
                "\n" +
                "	public nn_return_1() {/**/}\n" +
                "\n" +
                "	public /*@ non_null */ String m1(boolean returnNull) { \n" +
                "		if (returnNull) \n" +
                "			return null;\n" +
                "		else \n" +
                "			return \"hello\"; //$NON-NLS-1$\n" +
                "	}\n" +
                "	public /*@ nullable */ String m2(boolean returnNull) {\n" +
                "		if (returnNull) \n" +
                "			return null;\n" +
                "		else \n" +
                "			return \"hello\"; //$NON-NLS-1$\n" +
                "	}\n" +
                "\n" +
                "	public static void main(String[] args) {\n" +
                "		new nn_return_1().test();\n" +
                "	}\n" +
                "\n" +
                "	public void test() {\n" +
                "\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			this.m1(true);\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught good\"); //$NON-NLS-1$\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			this.m1(false);\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad\"); //$NON-NLS-1$\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 2\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			this.m2(true);\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad\"); //$NON-NLS-1$\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			this.m2(false);\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad\"); //$NON-NLS-1$\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 2\"); //$NON-NLS-1$\n" +
                "\n" +
                "	}\n" +
                "\n" +
                "	public static void fail(String msg) {\n" +
                "		System.out.println(\"failure: \"+msg); //$NON-NLS-1$\n" +
                "	}\n" +
                "}\n" 
			},
                "caught good\n" 
        );
    }
    public void _test_0036_nn_return_2() {
		this.runNegativeTest(
			new String[] {
				"nn_return_2.java",
                "\n" +
                "\n" +
                "public class nn_return_2 {\n" +
                "	public /*@ non_null */ String m1(boolean returnNull) { \n" +
                "		if (returnNull) \n" +
                "			return null;\n" +
                "		else \n" +
                "			return \"hello\"; //$NON-NLS-1$\n" +
                "	}\n" +
                "	public /*@ nullable */ String m2(boolean returnNull) {\n" +
                "		if (returnNull) \n" +
                "			return null;\n" +
                "		else \n" +
                "			return \"hello\"; //$NON-NLS-1$\n" +
                "	}\n" +
                "\n" +
                "	public static void main(String[] args) {\n" +
                "		nn_return_2 o = new nn_return_2();\n" +
                "\n" +
                "		boolean failed = true;\n" +
                "		try {\n" +
                "			o.m1(true);\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught good\"); //$NON-NLS-1$\n" +
                "			npe.printStackTrace();\n" +
                "			System.out.println();\n" +
                "			failed = false;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			o.m1(false);\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad\"); //$NON-NLS-1$\n" +
                "			npe.printStackTrace();\n" +
                "			System.out.println();\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m1 2\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			o.m2(true);\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad\"); //$NON-NLS-1$\n" +
                "			npe.printStackTrace();\n" +
                "			System.out.println();\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 1\"); //$NON-NLS-1$\n" +
                "\n" +
                "		failed = false;\n" +
                "		try {\n" +
                "			o.m2(false);\n" +
                "		} catch (NullPointerException npe) {\n" +
                "			System.out.println(\"caught bad\"); //$NON-NLS-1$\n" +
                "			npe.printStackTrace();\n" +
                "			System.out.println();\n" +
                "			failed = true;\n" +
                "		}\n" +
                "		if (failed) fail(\"m2 2\"); //$NON-NLS-1$\n" +
                "\n" +
                "	}\n" +
                "\n" +
                "	public static void fail(String msg) {\n" +
                "		System.out.println(\"failure: \"+msg); //$NON-NLS-1$\n" +
                "	}\n" +
                "}\n" 
			},
			"");
    }
    public void test_0040_RuntimeCast2() {
		this.runConformTest(
			new String[] {
				"RuntimeCast2.java",
                "\n" +
                "\n" +
                "public class RuntimeCast2 {\n" +
                "	public static void main(String[] args) {\n" +
                "		Object non = new RuntimeCast2();\n" +
                "		Object able = null;\n" +
                "\n" +
                "		non.hashCode();\n" +
                "		boolean failed = true;\n" +
                "       try {\n" +
                "			((/*@non_null*/ RuntimeCast2)able).hashCode();\n" +
                "       } catch (ClassCastException e) {\n" +
                "            failed = false;" +
                "	    }\n" +
                "       if (failed)\n"+
                "          System.out.println(\"failed\");\n"+
                "       else\n"+
                "          System.out.println(\"success!\");\n"+
                "	}\n" +
                "}\n" 
			},
			"success!");
    }

	public void test_0045_Runtime_Sanity() {
		this.runConformTest(
			new String[] {
				"Runtime_Sanity.java",
	            "import java.io.*;\n" +
	            "public class Runtime_Sanity {\n" +
	            "   public static void main(String [] args) {\n"+
	            "       PrintStream out = System.out;\n" +
	            "       if (out != null)\n" +
	            "           out.println(\"SUCCESS!\");\n"+
	            "   }\n"+
	            "}\n"
			},
			"SUCCESS!");
	}

	public void test_0046_Runtime_Return_RAC() {
		Map<String, String> options = getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.ENABLED);
		this.runConformTest(
			new String[] {
				"Runtime_Return_RAC.java",
	            "import java.io.*;\n" +
	            "public class Runtime_Return_RAC {\n" +
	            "   public static /*@nullable*/ String sm1() {return \"RAC Test\";}\n" +
	            "   public static /*@non_null*/ String sm2() {return \"RAC Test\";}\n" +
	            "   public static /*@nullable*/ String sm3() {return null;}\n" +
	            "   public static /*@non_null*/ String sm4() {return null;}\n" +                
	            "\n" +
	            "   public /*@nullable*/ String m1() {return \"RAC Test\";}\n" +
	            "   public /*@non_null*/ String m2() {return \"RAC Test\";}\n" +
	            "   public /*@nullable*/ String m3() {return null;}\n" +
	            "   public /*@non_null*/ String m4() {return null;}\n" +
	            "   public static void main(String [] args) {\n"+
	            "       boolean failed;\n"+
				"\n" +
				"       failed=false;\n"+
	            "       try {sm1();} catch (NullPointerException e) {failed=true;} finally {report(failed);}\n" +
				"       failed=false;\n"+
	            "       try {sm2();} catch (NullPointerException e) {failed=true;} finally {report(failed);}\n" +
				"       failed=false;\n"+
	            "       try {sm3();} catch (NullPointerException e) {failed=true;} finally {report(failed);}\n" +
				"       failed=true;\n"+
	            "       try {sm4();} catch (NullPointerException e) {failed=false;/*report(e.toString());*/} finally {report(failed);}\n" +
	            "\n" +
				"       Runtime_Return_RAC o = new Runtime_Return_RAC();\n" +
				"       failed=false;\n"+
	            "       try {o.m1();} catch (NullPointerException e) {failed=true;} finally {report(failed);}\n" +
				"       failed=false;\n"+
	            "       try {o.m2();} catch (NullPointerException e) {failed=true;} finally {report(failed);}\n" +
				"       failed=false;\n"+
	            "       try {o.m3();} catch (NullPointerException e) {failed=true;} finally {report(failed);}\n" +
				"       failed=true;\n"+
	            "       try {o.m4();} catch (NullPointerException e) {failed=false;} finally {report(failed);}\n" +
	            "   }\n"+
	            "   public static void report(boolean f) {\n" +
	            "       PrintStream out = System.out;\n" +
	            "       if (out != null)\n" +
	            "           if(f)\n" +
	            "              out.println(\"FAILURE!\");\n" +
	            "           else\n" +
	            "              out.println(\"SUCCESS!\");\n" +
	            "   }\n"+
	            "   public static void report(String s) {\n" +
	            "       PrintStream out = System.out;\n" +
	            "       if (out != null) \n" +
	            "              out.println(s);\n" +
	            "   }\n"+
	
	            "}\n"
			},
			"SUCCESS!\n" +
			"SUCCESS!\n" +
			"SUCCESS!\n" +
			"SUCCESS!\n" +
			"SUCCESS!\n" +
			"SUCCESS!\n" +
			"SUCCESS!\n" +
			"SUCCESS!",
			null, true, null, options, null);
	}
	public void test_0046_Runtime_CastNoType_RAC() {
		Map<String, String> options = getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.IGNORE);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.IGNORE);
		options.put(JmlCompilerOptions.OPTION_EnableRac, CompilerOptions.ENABLED);
		this.runConformTest(
			new String[] {
				"CastNoType.java",
	            "public class CastNoType {\n" +
	            "\n" +
	            "	public /*@non_null*/ Object m(/*@non_null*/ Object p) {\n" +
	            "		return /*@(non_null)*/ p;\n" +
	            "	}\n" +
	            "	public /*@non_null*/ Object n(/*@nullable*/ Object p) {\n" +
	            "		return /*@(non_null)*/ p;\n" +
	            "	}\n" +
	            "	public static void main(/*@non_null*/ String[] args) {\n" +
	            "		CastNoType o = new CastNoType();\n" +
	            "		boolean failed = false;\n" +
	            "		try {\n" +
	            "			o.m(args);\n" +
	            "		} catch (Exception e) {\n" +
	            "			failed = true;\n" +
	            "		}\n" +
	            "		report(failed, \"1\");\n" +
	            "		\n" +
	            "		failed = false;\n" +
	            "		try {\n" +
	            "			o.n(args);\n" +
	            "		} catch (Exception e) {\n" +
	            "			failed = true;\n" +
	            "		}\n" +
	            "		report(failed, \"2\");\n" +
	            "\n" +
	            "		failed = true;\n" +
//	            "		try {\n" +
//	            "			o.m(/*@(non_null)*/null);\n" +
//	            "		} catch (Exception e) {\n" +
	            "			failed = false;\n" +
//	            "		}\n" +
	            "		report(failed, \"3\");\n" +
	            "	}\n" +
	            "	private static void report(boolean failed, String string) {\n" +
	            "		if (failed)\n" +
	            "			System.out.println(\"failed at \"+string);\n" +
	            "		else\n" +
	            "			System.out.println(\"success at \"+string);\n" +
	            "   }\n" +
	            "}\n"
			},
			"success at 1\n" +
			"success at 2\n" +
			"success at 3",
			null, true, null, options, null);
	}
	public void test_1100_emptyReturn() {
		Map<String, String> options = getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_DefaultNullity, JmlCompilerOptions.NON_NULL);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.WARNING);
		this.runConformTest(
			new String[] {
					"X.java",
					"public class X {\n" +
					"	public void m1(/*@non_null*/ String s) {\n" +
					"		return;\n" +
					"	}\n" +
					"	public /*@non_null*/ String m2(/*@non_null*/ String s) {\n" +
					"		return s;\n" +
					"	}\n" +
		            "}\n"
			},
			"",
			null, true, null, options, null);
	}
}

