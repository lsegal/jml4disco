package org.jmlspecs.jml4.esc.provercoordinator.strategy;

import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public interface IProverStrategy {

	IProverStrategy[] EMPTY = new IProverStrategy[0];

	Result[] prove(VcProgram vcProg);

}
