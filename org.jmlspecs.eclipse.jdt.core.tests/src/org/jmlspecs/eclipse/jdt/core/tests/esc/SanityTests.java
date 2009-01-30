package org.jmlspecs.eclipse.jdt.core.tests.esc;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.text.MessageFormat;
import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.provercoordinator.prover.cvc3.Cvc3Adapter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.isabelle.IsabelleAdapter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.isabelle.IsabelleProcessPool;
import org.jmlspecs.jml4.esc.util.Utils;

public class SanityTests extends AbstractRegressionTest {
	public SanityTests(String name) {
		super(name);
	}

	// Augment problem detection settings
	@Override
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
		Map<String, String> options = super.getCompilerOptions();

		options.put(JmlCompilerOptions.OPTION_EnableJml, CompilerOptions.ENABLED);
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

	public void test_001_EscSanity() {
		this.runNegativeTest(new String[] { 
				"test_001_EscSanity.java",
				"public class test_001_EscSanity {\n" + 
				"  public void m() {}\n" + 
				"}\n" 
				}, 
				"");
	}

	public void test_002_CVC3() {
		String actual = "";
		String expected = "Valid.";
		Process p = null;
		try {
			p = Cvc3Adapter.getProverProcess();
			assertNotNull(p);
			OutputStream out = p.getOutputStream();
			out.write("QUERY TRUE;\n".getBytes());
			out.close();
			InputStream in = p.getInputStream();
			BufferedReader bis = new BufferedReader(new InputStreamReader(in));
			String line;
			while (null != (line = bis.readLine()))
				actual += line;
		} catch (IOException e) {
			fail(e.toString());
		}
		assertEquals(expected, actual);
	}

	public void test_003_simplify() {
		String actual = "";
		String expected = "1: Valid.";
		try {
			Process p = Runtime.getRuntime().exec("simplify");
			OutputStream out = p.getOutputStream();
			out.write("(EQ |@true| |@true|)\n".getBytes());
			out.close();
			InputStream in = p.getInputStream();
			BufferedReader bis = new BufferedReader(new InputStreamReader(in));
			String line;
			while (null != (line = bis.readLine()))
				actual += line;
		} catch (IOException e) {
			fail(e.toString());
		}
		assertTrue(actual.indexOf(expected) >= 0);
	}

	public void test_003_Isabelle() {
		String actual = "";
		String expected = "lemma main:";
		Process p = null;
		try {
			p = IsabelleProcessPool.getInstance().getFreeProcess();
			assertNotNull(p);
			OutputStream out = p.getOutputStream();
			String isabelleString = "theory test \nimports Main \nbegin \n" +
					  "lemma main: \"((5::int) = 3+2)\" \n" +
					  "by auto end\n";
			String baseFilename = "test";
			String wholeFilename = baseFilename + ".thy";
			Utils.writeToFile(wholeFilename, isabelleString);
			String USE_THY_CMD = "use_thy \"{0}\";\n"; //$NON-NLS-1$
			String command = MessageFormat.format(USE_THY_CMD, new String[]{baseFilename});

			out.write(command.getBytes());
			InputStream in = p.getInputStream();
			BufferedReader bis = new BufferedReader(new InputStreamReader(in));
			out.close();
			String line;
			while (null != (line = bis.readLine()))
				actual += line + "\n";
			bis.close();
			assertNotNull(p);
			Utils.deleteFile(wholeFilename);
		} catch (IOException e) {
			fail(e.toString());
		} finally {
			if (p != null)
				p.destroy();
		}
		assertTrue(actual.indexOf(expected) >= 0);
	}
}
