package org.jmlspecs.eclipse.jdt.core.tests.jml5;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class Jml5BasicTests extends AbstractRegressionTest {

	// While running tests we do not have access to the workspace, hence the follow cannot be used:
	// ResourcesPlugin.getWorkspace().getRoot().getLocation().toString();
	// For now, ".." seems to be the next best solution.
	public final String workspace = "..";
	public final String path2jml4annotations = workspace + "/org.jmlspecs.annotation/bin";

	public Jml5BasicTests(String name) {
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
        defaultClassPaths[length] = path2jml4annotations;
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
		options.put(JmlCompilerOptions.OPTION_SpecPath, Jml5BasicTests.getSpecPath());
		options.put(CompilerOptions.OPTION_Source, CompilerOptions.VERSION_1_6);
		options.put(CompilerOptions.OPTION_Compliance, CompilerOptions.VERSION_1_6);
		options.put(CompilerOptions.OPTION_Process_Annotations, CompilerOptions.ENABLED);
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

    public void test_0001_simpleModifiers() {
        this.runNegativeTest( new String[] {
                "X.java",
				"import org.jmlspecs.annotation.*;\n" +
                "public class X {\n"+
                "   @Nullable Object o1 = null;\n" +
                "   @NonNull  Object o2 = \"\";\n" +
                "	@Ghost int i;\n" +
                "   @Ghost int[] g = new int[3];\n" +
                "	@Pure int one() { return 1; }\n" +
                "}\n"
                },
                "");
    }
    public void test_0002a_lightweightMethodContractOk() {
        this.runNegativeTest( new String[] {
        		"X.java",
        		"import org.jmlspecs.annotation.*;\n" +
        		"public class X {\n"+
        		"   @Requires(\"true\")\n" +
        		"   @Assignable(\"\\nothing\")\n" +
        		"   @Ensures(redundantly = true, value = \"true\")\n" +
        		"   @Signals(\"(Exception e) true\")\n" +
        		"	public void m(int i) { i++; }\n" +
        		"}\n"
        },
		"");
    }
    public void test_0002b_lightweightMethodContractOk() {
        this.runNegativeTest( new String[] {
        		"X.java",
        		"import org.jmlspecs.annotation.*;\n" +
        		"public class X {\n"+
        		"   @Requires(\"true\")\n" +
        		"   @Assignable(\"\\nothing\")\n" +
        		"   @Ensures(redundantly = true, value = \"true\")\n" +
        		"   @Signals(\"(Exception e) true\")\n" +
        		"	public void m(int i) { i++; }\n" +
        		"}\n"
        },
		"");
    }
    public void test_0003_lightweightMethodContractErr() {
	    this.runNegativeTest( new String[] {
	    		"X.java",
	    		"import org.jmlspecs.annotation.*;\n" +
	    		"public class X {\n"+
	    		"   @Requires(\"true + 1\")\n" +
	    		"	public void m(int i) { i++; }\n" +
	    		"}\n"
	    },
		"----------\n" + 
		"1. ERROR in X.java (at line 1)\n" + 
		"	@Requires(\"true + 1\")\n" + 
		"	           ^^^^^^^^\n" + 
		"The operator + is undefined for the argument type(s) boolean, int\n" + 
		"----------\n");
	}

	public void test_0005_methodContract() {
    	// FIXME: this test will eventually fail once we start doing static checking ...
        this.runNegativeTest( new String[] {
                "X.java",
				"import org.jmlspecs.annotation.*;\n" +
                "public class X {\n"+
                "	@Also({\n" +
                "	  @SpecCase(\n" +
                "	    header = \"public normal_behavior\",\n" +
                "	    requires = \"amount > 0\",\n" +
                "	    assignable = \"balance\",\n" +
                "	    ensures = \"balance == \\\\old(balance) + amount\"),\n" +
                "	  @SpecCase(\n" +
                "	    header = \"public exceptional_behavior\",\n" +
                "	    requires = \"amount <= 0\",\n" +
                "	    assignable = \"\\\\nothing\",\n" +
                "	    signals = \"(Exception) amount <= 0\")\n" +
                "	})\n" +
                "	public void deposit(int amount) { }\n" +
                "}\n"
                },
                "");
    }

}
