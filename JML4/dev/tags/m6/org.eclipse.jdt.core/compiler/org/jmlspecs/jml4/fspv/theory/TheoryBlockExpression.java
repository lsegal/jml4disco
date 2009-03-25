package org.jmlspecs.jml4.fspv.theory;

public class TheoryBlockExpression extends TheoryExpression {
	public static final TheoryBlockExpression EMPTY_BLOCK = new TheoryBlockExpression(TheoryExpression.EMPTY, TheoryType.Bool());
	public final TheoryExpression[] expressions;

	public TheoryBlockExpression(TheoryExpression[] expressions, TheoryType type) {
		super(type);
		this.expressions = expressions;
	}
	
	public int size() {
		return this.expressions.length;
	}

	public TheoryExpression expressionAt(int i) {
		return this.expressions[i];
	}
}
