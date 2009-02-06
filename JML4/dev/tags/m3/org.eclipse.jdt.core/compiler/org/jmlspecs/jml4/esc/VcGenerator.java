package org.jmlspecs.jml4.esc;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.gc.lang.GcProgram;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;
import org.jmlspecs.jml4.util.Logger;

public class VcGenerator {

	protected final CompilerOptions options;
	protected final ProblemReporter problemReporter;
	private static final boolean DEBUG =false;

	public VcGenerator(CompilerOptions options,
			ProblemReporter problemReporter) {
		this.options = options;
		this.problemReporter = problemReporter;
	}

	// Stage 2: VC Generation
	// Stage 2.1: wlp semantics in intermediate VC language (IL) per block.
	public VcProgram process(GcProgram gc) {
		WlpVisitor visitor = new WlpVisitor();
		VcProgram result = gc.accept(visitor);
		if (DEBUG)
		   Logger.println(result.toString());
		return result;
	}
}
