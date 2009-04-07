// DISCO made only for benchmarking and printing results, used only in ProverStrategyFactory.make
// runs all the provers regardless of results for benchmarking

package org.jmlspecs.jml4.esc.provercoordinator.strategy;

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

public class ProveVcPiecewise_timings extends ProveVcPiecewise{

	public ProveVcPiecewise_timings(CompilerOptions options, ProblemReporter problemReporter, CachedVcs cachedVcs) {
	    super(options, problemReporter, cachedVcs);
	}

	public Result[] proveVc(VC vc, Map map) {
//		if (this.cachedVcs.contains(vc))
//			return Result.VALID;
		
		String methodName = vc.getName();
	
		long startTime;
		long simplifyTime, cvc3Time=0, negationTime=0, isabelleTime=0; 
		boolean simplifyProved, cvc3Proved=false, negationProved=false, isabelleProved=false;
		
		startTime = System.currentTimeMillis();
		// try to prove vc with Simplify, if successful, return valid result
		SimplifyAdapter simplify = new SimplifyAdapter(this.options, this.problemReporter);
		Result[] simplifyResults = simplify.prove(vc, map);
		simplifyTime = System.currentTimeMillis() - startTime;
		simplifyProved = Result.isValid(simplifyResults);
		Utils.assertTrue(simplifyResults.length > 0, "length of result array was zero"); //$NON-NLS-1$

		Result[] results = null;
		try {

			startTime = System.currentTimeMillis();
			// try to prove vc with CVC, if successful, return valid result
			Cvc3Adapter cvc = new Cvc3Adapter(this.options, this.problemReporter);			
			results = cvc.prove(vc, map);
			cvc3Time = System.currentTimeMillis() - startTime;
			cvc3Proved = Result.isValid(results);
		} catch (RuntimeException e) {
			if (DEBUG) throw e;
		}

		Result[] negatedResults = null;
		try {
			doingTheNegation = true;
			startTime = System.currentTimeMillis();
			VC negated = vc.negateLastImplication();
			negatedResults = simplify.prove(negated, map);
			negationTime = System.currentTimeMillis() - startTime;
			negationProved = Result.isValid(negatedResults);
		} catch (RuntimeException e) {
			if (DEBUG) throw e;
		} finally {
			doingTheNegation = false;
		}

		try {
			startTime = System.currentTimeMillis();
			// try to prove vc with Isabelle, if successful, return valid result
			IsabelleAdapter isabelle = new IsabelleAdapter(this.options, this.problemReporter);

			results = isabelle.prove(vc, map);
			isabelleTime = System.currentTimeMillis() - startTime;
			isabelleProved = Result.isValid(results);
		} catch (RuntimeException e) {
			if (DEBUG) throw e;
		}
		setVcName(simplifyResults, vc.getName());
		System.out.println ("pvpt\t"+vc.getName()+"\t"+
				            simplifyTime+"\t"+simplifyProved+"\t"+
				            cvc3Time+"\t"+cvc3Proved+"\t"+
				            negationTime+"\t"+negationProved+"\t"+
				            isabelleTime+"\t"+isabelleProved);
		
		if (simplifyProved || cvc3Proved || isabelleProved)
			return Result.VALID;
		return simplifyResults;
	}
}
