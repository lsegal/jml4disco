package org.jmlspecs.jml4.fspv.theory;

public class TheoryOldExpression extends TheoryExpression {

	public final TheoryExpression expression;

	public TheoryOldExpression(TheoryExpression e) {
		super(e.type);
		this.expression = e;
	}

	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}

}
