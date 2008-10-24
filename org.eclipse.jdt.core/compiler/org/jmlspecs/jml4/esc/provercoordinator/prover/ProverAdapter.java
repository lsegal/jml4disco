package org.jmlspecs.jml4.esc.provercoordinator.prover;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public abstract class ProverAdapter {

	public static final String VALID = "Valid."; //$NON-NLS-1$
	protected final CompilerOptions options;
	protected final ProblemReporter problemReporter;

	public ProverAdapter(CompilerOptions options, ProblemReporter problemReporter) {
		this.options = options;
		this.problemReporter = problemReporter;
	}

	public abstract Result[] prove(VC vc, Map incarnations);

}
