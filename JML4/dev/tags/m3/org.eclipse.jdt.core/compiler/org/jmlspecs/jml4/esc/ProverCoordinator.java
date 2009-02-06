package org.jmlspecs.jml4.esc;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.CachedVcs;
import org.jmlspecs.jml4.esc.provercoordinator.strategy.IProverStrategy;
import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProverStrategyFactory;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class ProverCoordinator {

	protected final CompilerOptions options;
	protected final ProblemReporter problemReporter;
	private final IProverStrategy strategy;

	public ProverCoordinator(CompilerOptions options,
			ProblemReporter problemReporter, CachedVcs cachedVcs) {
		this.options = options;
		this.problemReporter = problemReporter;
		this.strategy = ProverStrategyFactory.make(this.options.jmlEscProverStrategy, options, problemReporter, cachedVcs);
	}

	// FIXME: correct the comments below
	// Stage 3: Proving
	// Stage 3.1: IL to Prover Specific Language (PSL)
	// Stage 3.2: Prove (either as a whole or individual lemmas)
	// Stage 3.3: return Prover Independent Result
	public Result[] prove(VcProgram vc) {
		Result[] results = this.strategy.prove(vc);
		return results;
	}
	
	public String toString() {
		return "[ProverCoordinator: "+this.strategy.toString()+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
