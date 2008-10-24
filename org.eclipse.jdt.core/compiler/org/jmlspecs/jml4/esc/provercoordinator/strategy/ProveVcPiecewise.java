package org.jmlspecs.jml4.esc.provercoordinator.strategy;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.CachedVcs;
import org.jmlspecs.jml4.esc.provercoordinator.prover.cvc3.Cvc3Adapter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.isabelle.IsabelleAdapter;
import org.jmlspecs.jml4.esc.provercoordinator.prover.simplify.SimplifyAdapter;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class ProveVcPiecewise implements IProverStrategy {

	private static final boolean DEBUG = false;
	protected final CompilerOptions options;
	protected final ProblemReporter problemReporter;
	private CachedVcs cachedVcs;
	public static boolean doingTheNegation;

	public ProveVcPiecewise(CompilerOptions options, ProblemReporter problemReporter, CachedVcs cachedVcs) {
		this.options = options;
		this.problemReporter = problemReporter;
		this.cachedVcs = cachedVcs;
	}

	public static String getName() {
		return "ProveVcPiecewise"; //$NON-NLS-1$
	}

	public Result[] prove(VcProgram vcProg) {
		   VC[] vcs = vcProg.getAsImplications();
		   List/*<Result>*/ problems = new ArrayList(/*<Result>*/);
		   for (int i = 0; i < vcs.length; i++) {
			   VC vc = vcs[i];
			   vc.setName(vcProg.methodIndicator+"_"+(i+1)); //$NON-NLS-1$
			   Result[] results = proveVc(vc, vcProg.incarnations);
			   if (! Result.isValid(results)) {
				   for (int j = 0; j < results.length; j++) {
					   problems.add(results[j]);
				   }
			   }
		   }
		   if (problems.size() == 0)
			   problems.add(Result.VALID[0]);
		   return (Result[])problems.toArray(Result.EMPTY);
	}

	private Result[] proveVc(VC vc, Map map) {
		if (this.cachedVcs.contains(vc))
			return Result.VALID;

		// try to prove vc with Simplify, if successful, return valid result
		SimplifyAdapter simplify = new SimplifyAdapter(this.options, this.problemReporter);
		Result[] simplifyResults = simplify.prove(vc, map);
		Utils.assertTrue(simplifyResults.length > 0, "length of result array was zero"); //$NON-NLS-1$
		if (Result.isValid(simplifyResults)) {
			this.cachedVcs.add(vc);
			return simplifyResults;
		}

		Result[] results = null;
		try {
			// try to prove vc with CVC, if successful, return valid result
			Cvc3Adapter cvc = new Cvc3Adapter(this.options, this.problemReporter);
			results = cvc.prove(vc, map);
			if (Result.isValid(results)) {
				this.cachedVcs.add(vc);
				return results;
			}
		} catch (RuntimeException e) {
			if (DEBUG) throw e;
		}

		try {
			doingTheNegation = true;
			VC negated = vc.negateLastImplication();
			Result[] negatedResults = simplify.prove(negated, map);
			if (Result.isValid(negatedResults)) {
				this.cachedVcs.add(negated);
				setVcName(simplifyResults, "proved false"); //$NON-NLS-1$
				return simplifyResults;
			}
		} catch (RuntimeException e) {
			if (DEBUG) throw e;
		} finally {
			doingTheNegation = false;
		}

		try {
			// try to prove vc with Isabelle, if successful, return valid result
			IsabelleAdapter isabelle = new IsabelleAdapter(this.options, this.problemReporter);
			results = isabelle.prove(vc, map);
			if (Result.isValid(results)) {
				this.cachedVcs.add(vc);
				return results;
			}
		} catch (RuntimeException e) {
			if (DEBUG) throw e;
		}
		setVcName(simplifyResults, vc.getName());
		return simplifyResults;
	}

	private void setVcName(Result[] results, String name) {
//		Utils.assertTrue(results.length < 2, "there's more than a single result from simplify"); //$NON-NLS-1$
		for (int i = 0; i < results.length; i++) {
			results[i].setVcName(name);
		}
		System.getenv(name);
	}

	public String toString() {
		return "[ProveVcPiecewise: (Simplify, CVC3, Isabelle)]"; //$NON-NLS-1$
	}

}
