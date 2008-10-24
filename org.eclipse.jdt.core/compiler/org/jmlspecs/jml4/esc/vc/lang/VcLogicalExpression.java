package org.jmlspecs.jml4.esc.vc.lang;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;
import org.jmlspecs.jml4.esc.util.Utils;

public class VcLogicalExpression extends VcBinaryExpression {

	public final VcOperator operator;

	public VcLogicalExpression(VcOperator operator, VC left, VC right, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(left, right, TypeBinding.BOOLEAN, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		Utils.assertTrue(left.type == TypeBinding.BOOLEAN, "left is not a boolean but a '"+left.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		Utils.assertTrue(right.type == TypeBinding.BOOLEAN, "right is not a boolean but a '"+right.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		this.operator = operator;
	}

	public VcLogicalExpression(VcOperator operator, VC left, VC right, int sourceStart, int sourceEnd) {
		super(left, right, TypeBinding.BOOLEAN, sourceStart, sourceEnd);
		Utils.assertTrue(left.type == TypeBinding.BOOLEAN, "left is not a boolean but a '"+left.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		Utils.assertTrue(right.type == TypeBinding.BOOLEAN, "right is not a boolean but a '"+right.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		this.operator = operator;
	}

	public String toString() {
		return declString() + "[" + this.left + operator + this.right + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}
	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}
	public String acceptAsTerm(ProverVisitor visitor) {
		return visitor.visitAsTerm(this);
	}
	/*package*/ List/*<VC>*/  vc2vcs() {
		if (this.operator == VcOperator.IMPLIES) {
			List/*<VC>*/  rights = this.right.vc2vcs();
			List/*<VC>*/  result = new ArrayList(rights.size());
			for (Iterator iterator = rights.iterator(); iterator.hasNext();) {
				VC rhs = (VC) iterator.next();
				VcLogicalExpression newImplication = new VcLogicalExpression(VcOperator.IMPLIES, this.left, rhs, this.sourceStart, this.sourceEnd);
				newImplication.setLabel(this.kindOfAssertion(), this.kindOfLabel, this.labelStart());
				newImplication.addDecls(this.decls());
				result.add(newImplication);
			}
			return result;
		} else {
			return super.vc2vcs();
		}
	}

	public boolean endsInImpliesTrue() {
		return (this.operator == VcOperator.IMPLIES
			 ?  this.right.endsInImpliesTrue()
			 :  false);
	}

	public VC negateLastImplication() {
		VC result = (this.operator == VcOperator.IMPLIES
				  ?  new VcLogicalExpression(VcOperator.IMPLIES, this.left, this.right.negateLastImplication(), this.sourceStart, this.sourceEnd)
				  :  super.negateLastImplication());
		return result;
	}

	/*package*/ VC inline(Map map) {
		VC lefts = this.left.inlineAndAddDecls(map);
		VC rights = this.right.inlineAndAddDecls(map);
		if (this.left == lefts && this.right == rights)
			return this;
		return new VcLogicalExpression(this.operator, lefts, rights, this.sourceStart, this.sourceEnd);
	}
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
		result = prime * result + ((operator == null) ? 0 : operator.hashCode());
		return result;
	}

}
