package org.jmlspecs.jml4.esc.vc.lang;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;
import org.jmlspecs.jml4.esc.util.Utils;

public class VcQuantifiedExpression extends VC {

	public final VcQuantifier quantifier;
	public final VC range;
	public final VC body;
	private final VcVarDecl[] boundVarDecls;
	public final boolean isBlock;
	//@ invariant !isBlock ==> boundVarDecls == VcVarDecls.EMPTY;

	public VcQuantifiedExpression(VcQuantifier quantifier, VC range, VC body, TypeBinding type, KindOfAssertion kindOfAssertion, int kindOfLabel,int sourceStart, int sourceEnd, int labelStart) {
		super(type, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.quantifier = quantifier;
		this.range = range;
		this.body = body;
		this.isBlock = false;
		this.boundVarDecls = VcVarDecl.EMPTY;
		Utils.assertTrue(this.range != this.body, "range == body"); //$NON-NLS-1$
	}

	public VcQuantifiedExpression(VcQuantifier quantifier, VC range, VC body, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.quantifier = quantifier;
		this.range = range;
		this.body = body;
		this.isBlock = false;
		this.boundVarDecls = VcVarDecl.EMPTY;
		Utils.assertTrue(this.range != this.body, "range == body"); //$NON-NLS-1$
	}

	public VcQuantifiedExpression(VcQuantifier quantifier, VcVarDecl[] boundVarDecls, VC body) {
		super(TypeBinding.BOOLEAN, 0, 0);
		this.quantifier = quantifier;
		this.range = VcBooleanConstant.TRUE;
		this.body = body;
		this.boundVarDecls = boundVarDecls;
		this.isBlock = true;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public String acceptAsTerm(ProverVisitor visitor) {
		return visitor.visitAsTerm(this);
	}

	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + range.hashCode();
		result = prime * result + body.hashCode();
		result = prime * result + quantifier.hashCode();
		return result;
	}

	/*package*/ VC inline(Map map) {
		VC ranges = this.range.inlineAndAddDecls(map);
		VC bodys = this.body.inlineAndAddDecls(map);
		if (this.range == ranges && this.body== bodys)
			return this;
		VC result = (this.isBlock)
			      ? new VcQuantifiedExpression(this.quantifier, this.boundVarDecls, bodys)
			      : new VcQuantifiedExpression(this.quantifier, ranges, bodys, this.type, this.sourceStart, this.sourceEnd);
	    return result;
	}

	public String toString() {
		if (this.isBlock) {
			return declString() + "(block " + Arrays.asList(this.boundVarDecls) + " : " +  this.body + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		} else {
			return declString() + "(" + this.quantifier +  //$NON-NLS-1$
            		this.range.decls() + " ; " + //$NON-NLS-1$
            		this.range + " ; " + this.body + ")"; //$NON-NLS-1$ //$NON-NLS-2$
		}
	}

	/*package*/ List/*<VC>*/ vc2vcs() {
		List/*<VC>*/ result;
		if (this.isBlock) {
			List/*<VC>*/ fromBody = this.body.vc2vcs();
			result = new ArrayList/*<VC>*/(fromBody.size());
			for (Iterator iterator = fromBody.iterator(); iterator.hasNext();) {
				VC bodyVc = (VC) iterator.next();
				VC newVc = new VcQuantifiedExpression(this.quantifier, this.boundVarDecls, bodyVc);
				result.add(newVc);
			}
		} else {
			result = super.vc2vcs();
		}
		return result;
	}

	public VcVarDecl[] boundVarDecls() {
		return this.boundVarDecls;
	}
}
