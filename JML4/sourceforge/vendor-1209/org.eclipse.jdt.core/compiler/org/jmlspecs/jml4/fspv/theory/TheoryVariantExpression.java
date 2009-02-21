package org.jmlspecs.jml4.fspv.theory;

public class TheoryVariantExpression extends TheoryBlockExpression {

	public static final TheoryVariantExpression EMPTY_VARIANT = new TheoryVariantExpression(TheoryExpression.EMPTY);

	public TheoryVariantExpression(TheoryExpression[] expressions) {
		super(expressions, TheoryType.Nat());
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
