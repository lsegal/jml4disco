package org.jmlspecs.jml4.fspv.theory;

public class TheoryInvariantExpression extends TheoryBlockExpression {
	public static final TheoryInvariantExpression EMPTY_INVARIANT = new TheoryInvariantExpression(TheoryExpression.EMPTY);

	public TheoryInvariantExpression(TheoryExpression [] expressions) {
		super(expressions, TheoryType.Bool());
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}

}
