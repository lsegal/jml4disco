package org.jmlspecs.jml4.esc.vc.lang;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcAnd extends VcBinaryExpression {

	public VcAnd(VC left, VC right, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(left, right, TypeBinding.BOOLEAN, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
	}

	public VcAnd(VC left, VC right, int sourceStart, int sourceEnd) {
		super(left, right, TypeBinding.BOOLEAN, sourceStart, sourceEnd);
	}

	public String toString() {
		return declString() + "[" + this.left + "/\\" + this.right + "]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public String acceptAsTerm(ProverVisitor visitor) {
		return visitor.visitAsTerm(this);
	}

	/*package*/ List/*<VC>*/  vc2vcs() {
		if (this.kindOfAssertion() != null) {
			if (this.left.kindOfAssertion() == null) {
				left.setLabel(this.kindOfAssertion(), this.kindOfLabel, this.labelStart());
			}
			if (this.right.kindOfAssertion() == null) {
				right.setLabel(this.kindOfAssertion(), this.kindOfLabel, this.labelStart());
				right.kindOfLabel = this.kindOfLabel;
			}
		}
		List/*<VC>*/  lefts = this.left.vc2vcs();
		List/*<VC>*/  rights = this.right.vc2vcs();
		List/*<VC>*/  result = new ArrayList();
		result.addAll(lefts);
		result.addAll(rights);
		return result;
	}

	/*package*/ VC inline(Map map) {
		VC lefts = this.left.inlineAndAddDecls(map);
		VC rights = this.right.inlineAndAddDecls(map);
		if (this.left == lefts && this.right == rights)
			return this;
		return new VcAnd(lefts, rights, this.sourceStart, this.sourceEnd);
	}
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + left.hashCode();
		result = prime * result + right.hashCode();
		return result;
	}
}
