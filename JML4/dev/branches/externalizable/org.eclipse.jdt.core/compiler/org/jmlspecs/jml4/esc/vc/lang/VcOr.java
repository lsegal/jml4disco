package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcOr extends VcBinaryExpression {

	public VcOr() {}
	
	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		super.readExternal(in);
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		super.writeExternal(out);
	}
	
	public VcOr(VC left, VC right, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(left, right, TypeBinding.BOOLEAN, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
	}

	public VcOr(VC left, VC right, int sourceStart, int sourceEnd) {
		super(left, right, TypeBinding.BOOLEAN, sourceStart, sourceEnd);
	}

	public String toString() {
		return declString() + "[" + this.left + "\\/" + this.right + "]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public String acceptAsTerm(ProverVisitor visitor) {
		return visitor.visitAsTerm(this);
	}

	/*package*/ VC inline(Map map) {
		VC lefts = this.left.inlineAndAddDecls(map);
		VC rights = this.right.inlineAndAddDecls(map);
		if (this.left.equals(lefts) && this.right.equals(rights))
			return this;
		return new VcOr(lefts, rights, this.sourceStart, this.sourceEnd);
	}

	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
		return result;
	}
}
