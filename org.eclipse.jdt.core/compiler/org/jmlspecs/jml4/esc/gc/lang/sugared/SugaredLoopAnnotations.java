package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredOperator;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredLoopAnnotations {
	
	public final SugaredExpression[] invariants;
	public final SugaredExpression[] variants;
	private SugaredExpression foldedInvariants;

	//@ requires (* all i: invariants[i].type == BOOLEAN *);
	//@ requires (* all i: variants[i].type   == INT     *);
	public SugaredLoopAnnotations(SugaredExpression[] invariants, SugaredExpression[] variants) {
		this.invariants = invariants;
		this.variants = variants;
	}
	public SugaredExpression foldInvariants() {
		if (this.foldedInvariants == null) {
			SugaredExpression folded;
			if (this.invariants.length==0) {
				folded = new SugaredBooleanConstant(true, 0, 0);
			} else {
				folded = this.invariants[this.invariants.length-1];
				for (int i = this.invariants.length-2; i >= 0; i--) {
					//TODO: replace the AND below with AND_AND
					folded = new SugaredBinaryExpression(SugaredOperator.AND, this.invariants[i], folded, folded.type, this.invariants[i].sourceStart, folded.sourceEnd);
				}
			}
			if (this.variants.length > 0) {
				for (int i = 0; i < variants.length; i++) {
					SugaredExpression variant = this.variants[i];
					SugaredExpression variantGeqZero = new SugaredBinaryExpression(SugaredOperator.GREATER_EQUALS, variant, SugaredIntegerConstant.ZERO, TypeBinding.INT, variant.sourceStart, variant.sourceEnd);
					folded = new SugaredBinaryExpression(SugaredOperator.AND, folded, variantGeqZero, folded.type, folded.sourceStart, folded.sourceEnd);
				}
			}
			this.foldedInvariants = folded;
		}
		return this.foldedInvariants;
	}
	public String toString() {
		return "(inv: "+Utils.toString(this.invariants)+", var:"+Utils.toString(this.variants)+")";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
	}
}