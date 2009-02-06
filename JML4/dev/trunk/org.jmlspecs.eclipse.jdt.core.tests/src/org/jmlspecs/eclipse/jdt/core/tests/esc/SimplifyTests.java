package org.jmlspecs.eclipse.jdt.core.tests.esc;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.Map;

import org.eclipse.jdt.core.tests.compiler.regression.AbstractRegressionTest;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.provercoordinator.prover.simplify.SimplifyAdapter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.simplify.SimplifyProcessPool;
import org.jmlspecs.jml4.esc.result.lang.Result;

public class SimplifyTests extends AbstractRegressionTest {
	public SimplifyTests(String name) {
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
	public void test_000_simplify_sanity() {
		String actual = "";
		String expected = "1: Valid.";
		try {
			Process p = SimplifyProcessPool.getInstance().getFreeProcess();
			assertNotNull(p);
			OutputStream out = p.getOutputStream();
			out.write("(EQ |@true| |@true|)\n".getBytes());
			out.close();
			InputStream in = p.getInputStream();
			BufferedReader bis = new BufferedReader(new InputStreamReader(in));
			String line;
			while (null != (line = bis.readLine()))
				actual += line;
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		assertTrue("Actually got " + actual, actual.indexOf(expected) >= 0);
	}
	public void test_001_formatResults() {
		String simplifyString = "(IMPLIES (AND (IFF (EQ |Start$ok| |@true|) (LBLNEG |Assume@56| (IMPLIES (AND "+
		"(LBLNEG |var@38| (EQ |@true| (is |x$38| T_int)))) "+
		"(LBLNEG |implies@56_70| (IMPLIES (EQ |@true| (integralLE 100 |x$38@0|)) (LBLNEG |Assert@83| (LBLNEG |and@83_94| "+ 
		"(AND (LBLNEG |const@90_94| (EQ |@true| |bool$false|) ) (LBLNEG |Assert@127| (LBLNEG |and@127_127| (AND (LBLNEG |eq@122_127| "+ 
		"(EQ |@true| (integralLE 0 |x$38@0|))) (LBLNEG |and@0_0| (AND (EQ |@true| |jmlWhile$1$header$ok| ) (LBLNEG |const@0_0|  "+
		"(EQ |@true| |@true|) ))))))))))))) ) (IFF (EQ |jmlWhile$1$header$ok| |@true|) (LBLNEG |Assert@0| (LBLNEG |and@0_0|  "+
		"(AND (LBLNEG |const@0_0| (EQ |@true| |@true|) ) (LBLNEG |Assume@127| (LBLNEG |implies@127_127| (IMPLIES (EQ |@true|  "+
		"(integralLE 0 |x$38@1|)) (LBLNEG |and@0_0| (AND (EQ |@true| |jmlWhile$1$body$ok| ) (LBLNEG |and@0_0| (AND (EQ |@true|  "+
		"|jmlWhile$1$after$ok| ) (LBLNEG |const@0_0| (EQ |@true| |@true|) ))))))))))) ) (IFF (EQ |jmlWhile$1$body$ok| |@true|) "+
		"(LBLNEG |Assume@147| (LBLNEG |implies@147_147| (IMPLIES (EQ |@true| (integralLT 0 |x$38@1|)) (LBLNEG |Assume@162|  "+
		"(LBLNEG |implies@162_0| (IMPLIES (EQ |@true| (integralEQ |x$38@1| |x$38@1|)) (LBLNEG |Assume@168| (LBLNEG |implies@168_166| "+ 
		"(IMPLIES (EQ |@true| (integralEQ |x$38@2| (- |x$38@1| 2))) (LBLNEG |Assert@127| (LBLNEG |and@127_127|  "+
		"(AND (LBLNEG |eq@122_127| (EQ |@true| (integralLE 0 |x$38@2|))) (LBLNEG |const@0_0| (EQ |@true| |@true|) )) "+
		"))))))))))) ) (IFF (EQ |jmlWhile$1$after$ok| |@true|) (LBLNEG |Assume@147| (LBLNEG |implies@147_143| (IMPLIES (NOT "+ 
		"(EQ |@true| (integralLT 0 |x$38@1|))) (LBLNEG |and@0_0| (AND (EQ |@true| |jmlWhile$1$break$ok| ) (LBLNEG |const@0_0|  "+
		"(EQ |@true| |@true|) )))))) ) (IFF (EQ |jmlWhile$1$break$ok| |@true|) (LBLNEG |Assume@190| (IMPLIES (AND (LBLNEG |var@181| "+ 
		"(EQ |@true| (is |result$181| T_int)))) (LBLNEG |implies@190_186| (IMPLIES (EQ |@true| (integralEQ |result$181@1|  "+
		"|x$38@1|)) (LBLNEG |Assert@203| (LBLNEG |and@203_220| (AND (LBLNEG |eq@210_220| (EQ |@true| (integralNE |result$181@1| "+
		"0))) (LBLNEG |Assert@0| (LBLNEG |and@0_0| (AND (LBLNEG |const@0_0| (EQ |@true| |@true|) ) (LBLNEG |const@0_0|  "+
		"(EQ |@true| |@true|) ))))))))))) ) ) (EQ |@true| |Start$ok|)) ";

		String labels = " 1: Invalid.\n" +
		                "labels: (|Assert@127| |and@0_0| |Assume@127| |implies@168_166| |Assert@203| |eq@210_220| " + 
		                         "|Assume@162| |eq@122_127| |implies@162_0| |and@203_220| |implies@127_127| |Assert@83| " + 
		                         "|implies@147_147| |and@127_127| |Assume@147| |const@90_94| |and@83_94| |Assume@168| " + 
		                         "|Assert@0| |implies@190_186| |Assume@190| |implies@56_70| |Assume@56|)";

		SimplifyAdapter simplify = new SimplifyAdapter(null, null);
		Result[] actual = simplify.formatResponse(labels, null, simplifyString);
		String[] expected = {"[Result: Assert(203) at (210, 220)]", 
				             "[Result: Assert(127) at (122, 127)]", 
				             "[Result: Assert(83) at (90, 94)]"};
		assertEquals(expected.length, actual.length);
		for (int i = 0; i < expected.length; i++) {
			assertEquals(expected[i], actual[i].toString());
		}
	}
}
