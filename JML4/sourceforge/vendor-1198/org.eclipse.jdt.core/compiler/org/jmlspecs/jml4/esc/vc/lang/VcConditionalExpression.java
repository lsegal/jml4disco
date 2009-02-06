package org.jmlspecs.jml4.esc.vc.lang;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcConditionalExpression extends VC {

	public final VC condition;
	public final VC valueIfTrue;
	public final VC valueIfFalse;

	public VcConditionalExpression(VC condition, 
			VC valueIfTrue, VC valueIfFalse, 
			TypeBinding type, KindOfAssertion kindOfAssertion, 
			int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(type, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.condition = condition;
		this.valueIfTrue = valueIfTrue;
		this.valueIfFalse = valueIfFalse;
	}

	public VcConditionalExpression(VC condition, 
			VC valueIfTrue, VC valueIfFalse, 
			TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.condition = condition;
		this.valueIfTrue = valueIfTrue;
		this.valueIfFalse = valueIfFalse;
	}

	/*package*/ List/*<VC>*/  vc2vcs() {
		boolean isAndAnd = isAndAnd();
		if (isAndAnd) {
			if (this.kindOfAssertion() != null) {
				if (this.condition.kindOfAssertion() == null) {
					this.condition.setLabel(this.kindOfAssertion(), this.kindOfLabel, this.labelStart());
				}
				if (this.valueIfTrue.kindOfAssertion() == null) {
					this.valueIfTrue.setLabel(this.kindOfAssertion(), this.kindOfLabel, this.labelStart());
				}
			}
			VC newRight = new VcLogicalExpression(VcOperator.IMPLIES, this.condition, this.valueIfTrue, 0, 0);
			List/*<VC>*/  lefts = this.condition.vc2vcs();
			List/*<VC>*/  rights = newRight.vc2vcs();
			List/*<VC>*/  result = new ArrayList();
			result.addAll(lefts);
			result.addAll(rights);
			return result;
		}
		return super.vc2vcs();
	}

	private boolean isAndAnd() {
		// && has a litteral false for its ifFalse value
		if (! (this.valueIfFalse instanceof VcBooleanConstant))
			return false;
		if (((VcBooleanConstant)this.valueIfFalse).value)
			return false;

		// || has a litteral true for its ifTrue value
		if (this.valueIfTrue instanceof VcBooleanConstant)
			if (((VcBooleanConstant)this.valueIfTrue).value)
				return false;
		return true;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}
	public String acceptAsTerm(ProverVisitor visitor) {
		return visitor.visitAsTerm(this);
	}

	public String toString() {
		return "( " + this.condition + " ? " + //$NON-NLS-1$//$NON-NLS-2$
				this.valueIfTrue + " : " + this.valueIfFalse + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public List/*<VcVarDecl>*/ getVarDecls() {
		List/*<VcVarDecl>*/ result= new ArrayList/*<VcVarDecl>*/();
		result.addAll(this.decls());
		result.addAll(this.condition.decls());
		result.addAll(this.valueIfTrue.decls());
		result.addAll(this.valueIfFalse.decls());
		return result;
	}
	/*package*/ VC inline(Map map) {
		VC conds = this.condition.inlineAndAddDecls(map);
		VC trues = this.valueIfTrue.inlineAndAddDecls(map);
		VC falses = this.valueIfFalse.inlineAndAddDecls(map);
		if (this.condition == conds && this.valueIfTrue == trues && this.valueIfFalse == falses)
			return this;
		return new VcConditionalExpression(conds, trues, falses, this.type, this.sourceStart, this.sourceEnd);
	}
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((condition == null) ? 0 : condition.hashCode());
		result = prime * result + ((valueIfTrue == null) ? 0 : valueIfTrue.hashCode());
		result = prime * result + ((valueIfFalse == null) ? 0 : valueIfFalse.hashCode());
		return result;
	}
}
