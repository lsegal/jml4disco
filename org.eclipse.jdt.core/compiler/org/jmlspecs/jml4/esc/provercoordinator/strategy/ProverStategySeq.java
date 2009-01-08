package org.jmlspecs.jml4.esc.provercoordinator.strategy;

import java.util.Arrays;
import java.util.List;

import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class ProverStategySeq implements IProverStrategy {

	private final IProverStrategy[] strategies;

	public ProverStategySeq(IProverStrategy[] strategies) {
		this.strategies = strategies;
	}

	public ProverStategySeq(List list) {
		this.strategies = (IProverStrategy[])list.toArray(IProverStrategy.EMPTY);
	}

	public Result[] prove(VcProgram vcProg) {
		Result[] result = Result.EMPTY;
		for (int i = 0; i < this.strategies.length; i++) {
			result = this.strategies[i].prove(vcProg);
			if (Result.isValid(result))
				return result;
		}
		return result;
	}

	public String toString() {
		return "[ProverStategySeq: "+Arrays.asList(strategies).toString()+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
