package org.jmlspecs.jml4.fspv.theory;

public class TheoryLoopAnnotationsExpression extends TheoryExpression {

	public static final TheoryLoopAnnotationsExpression EMPTY_LOOP_ANNOTATIONS = new TheoryLoopAnnotationsExpression(TheoryInvariantExpression.EMPTY_INVARIANT, TheoryVariantExpression.EMPTY_VARIANT);
	public final TheoryInvariantExpression invariant;
	public final TheoryVariantExpression variant;

	public TheoryLoopAnnotationsExpression(TheoryInvariantExpression invariant, TheoryVariantExpression variant) {
		super(TheoryType.Bool());
		this.invariant = invariant;
		this.variant = variant;
	}
	
	public int invariantSize() {
		return this.invariant.size();
	}
	
	public TheoryExpression invariantAt(int i) {
		return this.invariant.expressionAt(i);
	}

	public int variantSize() {
		return this.variant.size();
	}

	public TheoryExpression variantAt(int i) {
		return this.variant.expressionAt(i);
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
