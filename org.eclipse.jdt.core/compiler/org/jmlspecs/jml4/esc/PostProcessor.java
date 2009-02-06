package org.jmlspecs.jml4.esc;

import java.io.File;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.util.Counter;

public class PostProcessor {

	protected final CompilerOptions options;
	protected final ProblemReporter problemReporter;
	protected final Counter counter;
	public static boolean useOldErrorReporting = false;

	public PostProcessor(CompilerOptions options,
			ProblemReporter problemReporter, Counter counter) {
		this.options = options;
		this.problemReporter = problemReporter;
		this.counter = counter;
	}

	// Stage 4: Post-processing
	// Stage 4.1: process prover output and update UI.
	public void postProcess(Result[] results, int sourceStart) {
		process(results, sourceStart);
	}

	protected void process(Result[] results, int sourceStart) {
		results = Result.removeDuplicates(results);
		for (int i = 0; i < results.length; i++) {
			Result result = results[i];
			if (result.isValid())
				continue;

			String msg = getMessage(result.kindOfAssertion());
			int start = result.failedExprStart();
			int end   = result.failedExprEnd();
			if (start <= 0) {
				start = sourceStart;
				end = sourceStart + 1;
			}
            String vcName = result.vcName();
            if (vcName == null) {
            	vcName = "unknown"; //$NON-NLS-1$
            }
            int pos = vcName.lastIndexOf(File.separator);
            if (pos >= 0)
            	vcName = vcName.substring(pos+1);
			if (!useOldErrorReporting && result.kindOfAssertion() == KindOfAssertion.ASSERT)
				msg += " ("+vcName+")";  //$NON-NLS-1$//$NON-NLS-2$
            this.problemReporter.jmlEsc2Error(msg, start, end);
            if (useOldErrorReporting || result.kindOfAssertion() == KindOfAssertion.ASSERT)
               continue;
            int assertionPosition = result.assertionPosition();
			if (assertionPosition > 0)
            	this.problemReporter.jmlEsc2Error(msg + " ("+vcName+")", assertionPosition, assertionPosition); //$NON-NLS-1$ //$NON-NLS-2$
		}
	}

	private String getMessage(KindOfAssertion kindOfAssertion) {
		if (kindOfAssertion == KindOfAssertion.UNKNOWN)
			return "Unknown ESC error"; //$NON-NLS-1$
		if (useOldErrorReporting)
		   return "Possible assertion failure ("+kindOfAssertion+")."; //$NON-NLS-1$ //$NON-NLS-2$
		return "Possible assertion failure - "+counter.getAndIncCounter()+" - ("+kindOfAssertion+")."; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}
}
