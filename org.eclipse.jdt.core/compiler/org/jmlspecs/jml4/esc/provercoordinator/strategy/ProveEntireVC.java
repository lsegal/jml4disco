package org.jmlspecs.jml4.esc.provercoordinator.strategy;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.Esc;
import org.jmlspecs.jml4.esc.provercoordinator.prover.CachedVcs;
import org.jmlspecs.jml4.esc.provercoordinator.prover.simplify.SimplifyAdapter;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class ProveEntireVC implements IProverStrategy {

	protected final CompilerOptions options;
	protected final ProblemReporter problemReporter;
	private CachedVcs cachedVcs;
	public static boolean active = false;

	public ProveEntireVC(CompilerOptions options, ProblemReporter problemReporter, CachedVcs cachedVcs) {
		this.options = options;
		this.problemReporter = problemReporter;
		this.cachedVcs = cachedVcs;
	}

	public static String getName() {
		return "ProveEntireVC"; //$NON-NLS-1$
	}

	public Result[] prove(VcProgram vcProg) {

		if (this.cachedVcs.contains(vcProg))
			return Result.VALID;
		this.active  = true;
		SimplifyAdapter simplify = new SimplifyAdapter(this.options, this.problemReporter);
		VC vc = vcProg.getAsSingleVC()[0];
		Result[] results = simplify.prove(vc, vcProg.incarnations);
		Utils.assertTrue(results.length > 0, "length of result array was zero"); //$NON-NLS-1$
		if (Result.isValid(results)) {
			this.cachedVcs.add(vcProg);
		}
		this.active = false;

		return results;
	}
	
	public String toString() {
		return "[ProveEntireVC(with Simplify)]"; //$NON-NLS-1$
	}

}
