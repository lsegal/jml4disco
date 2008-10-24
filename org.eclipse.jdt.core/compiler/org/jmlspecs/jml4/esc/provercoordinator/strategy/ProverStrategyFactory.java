package org.jmlspecs.jml4.esc.provercoordinator.strategy;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.CachedVcs;

public class ProverStrategyFactory {

	public static IProverStrategy make(String jmlEscProverStrategy, CompilerOptions options, ProblemReporter problemReporter, CachedVcs cachedVcs) {
		String[] args = jmlEscProverStrategy.length() == 0
				      ? new String[] {ProveEntireVC.getName(), ProveVcPiecewise.getName()}
					  : jmlEscProverStrategy.split(" "); //$NON-NLS-1$
		List/*<IProverStrategy>*/ list = new ArrayList/*<IProverStrategy>*/();
		for (int i = 0; i < args.length; i++) {
			if (args[i].equals(ProveEntireVC.getName()))
				list.add(new ProveEntireVC(options, problemReporter, cachedVcs));
			else if (args[i].equals(ProveVcPiecewise.getName()))
				list.add(new ProveVcPiecewise(options, problemReporter, cachedVcs));
		}
		return list.size() == 1
			 ? (IProverStrategy)list.get(0)
			 : new ProverStategySeq(list);
	}

}
