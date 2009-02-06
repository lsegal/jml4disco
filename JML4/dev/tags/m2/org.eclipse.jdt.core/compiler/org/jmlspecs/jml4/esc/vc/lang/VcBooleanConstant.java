package org.jmlspecs.jml4.esc.vc.lang;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public final class VcBooleanConstant extends VC {

	public static final VcBooleanConstant TRUE = new VcBooleanConstant(true, 0, 0);
	public  final boolean value;
	private final String name;

	
	public VcBooleanConstant(boolean value, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(TypeBinding.BOOLEAN, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.value = value;
		this.name = value ? "True" : "False"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public VcBooleanConstant(boolean value, int sourceStart, int sourceEnd) {
		super(TypeBinding.BOOLEAN, sourceStart, sourceEnd);
		this.value = value;
		this.name = value ? "True" : "False"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public String toString() {
		return declString() + this.name;
	}
	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}
	public String acceptAsTerm(ProverVisitor visitor) {
		return visitor.visitAsTerm(this);
	}
	/*package*/ VC inline(Map map) {
		return this;
	}
	public int hashCode() {
		final int prime = 31;
		int result = ((value) ? prime : 1);
		return result;
	}
	public boolean endsInImpliesTrue() {
		return this.value;
	}
}
