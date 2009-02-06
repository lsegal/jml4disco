package org.jmlspecs.eclipse.jdt.core.tests.esc;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.text.MessageFormat;

import org.jmlspecs.jml4.esc.provercoordinator.prover.cvc3.Cvc3Adapter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.isabelle.IsabelleProcessPool;
import org.jmlspecs.jml4.esc.util.Utils;

public class SanityTests extends EscTest {
	public SanityTests(String name) {
		super(name);
	}

	public void test_001_EscSanity() {
		this.runNegativeTest(new String[] { 
				testsPath + "test_001_EscSanity.java",
				"package tests.esc;\n" +
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
			String command = MessageFormat.format(USE_THY_CMD, new Object[]{baseFilename});

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
