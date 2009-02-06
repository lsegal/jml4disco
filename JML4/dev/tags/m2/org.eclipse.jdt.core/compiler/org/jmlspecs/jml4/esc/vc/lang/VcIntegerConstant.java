package org.jmlspecs.jml4.esc.vc.lang;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcIntegerConstant extends VC {

	public static final VcIntegerConstant ZERO = new VcIntegerConstant(0, 0, 0);
	public final int value;

	public VcIntegerConstant(int value, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(TypeBinding.INT, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.value = value;
	}

	public VcIntegerConstant(int value, int sourceStart, int sourceEnd) {
		super(TypeBinding.INT, sourceStart, sourceEnd);
		this.value = value;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "" + this.value; //$NON-NLS-1$
	}
	/*package*/ VC inline(Map map) {
		return this;
	}
	public int hashCode() {
		final int prime = 31;
		int result = prime * value;
		return result;
	}
}
