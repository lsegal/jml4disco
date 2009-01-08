package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class DataGroupTestCompiler extends AbstractRegressionTest {

	public DataGroupTestCompiler(String name) {
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
	    options.put(CompilerOptions.OPTION_ReportNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportPotentialNullReference, CompilerOptions.ERROR);
	    options.put(CompilerOptions.OPTION_ReportRedundantNullCheck, CompilerOptions.ERROR);
	    options.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, CompilerOptions.ERROR);
//		options.put(CompilerOptions.OPTION_ReportRawTypeReference, CompilerOptions.ERROR);
//		options.put(CompilerOptions.OPTION_ReportUnnecessaryElse, CompilerOptions.ERROR);
//		options.put(CompilerOptions.OPTION_ReportUnusedLocal, CompilerOptions.ERROR);
		options.put(JmlCompilerOptions.OPTION_SpecPath, DbcTestCompiler.getSpecPath());
	    return options;
	}

    public void test_0001_inObjectState() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   Object o; //@ in ObjectState;\n" +
                "   public void m(int i) {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0002_inRedundantly() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   Object o; //@ in_redundantly ObjectState;\n" +
                "   public void m(int i) {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0003_inObjectState() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   Object o; //@ in this.x;\n" +
                "   public void m(int i) {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0004_inObjectState() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   Object o; //@ in super.x;\n" +
                "   public void m(int i) {} \n" +
                "}\n"
                },
                "");
    }
    public void test_0005_mapsInto() {
        this.runNegativeTest( new String[] {
                "X.java",
                "public class X {\n"+
                "   Object o; //@ maps x.y \\into z;\n" +
                "   public void m(int i) {} \n" +
                "}\n"
                },
                "");
    }
}
