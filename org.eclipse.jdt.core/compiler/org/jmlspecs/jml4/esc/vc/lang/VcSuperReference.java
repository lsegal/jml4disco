package org.jmlspecs.jml4.esc.vc.lang;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcSuperReference extends VcThisReference {

	
	public VcSuperReference(TypeBinding type, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(type, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
	}

	public VcSuperReference(TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public int hashCode() {
		int prime = 31;
		int result = 1;
		result = result * prime + "super".hashCode(); //$NON-NLS-1$
		result = result * prime + this.sourceStart;
		return result;
	}

	VC inline(Map map) {
		return this;
	}

	public String toString() {
		return "[super]"; //$NON-NLS-1$
	}

}
