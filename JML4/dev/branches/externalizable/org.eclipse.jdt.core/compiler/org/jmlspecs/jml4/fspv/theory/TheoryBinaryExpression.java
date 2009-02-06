package org.jmlspecs.jml4.fspv.theory;


public class TheoryBinaryExpression extends TheoryExpression {

	public final TheoryExpression	lhs;
	public final TheoryOperator	op;
	public final TheoryExpression	rhs;


	public TheoryBinaryExpression(TheoryExpression l, TheoryOperator op, TheoryExpression r) {
		super(l.type);
		this.lhs = l;
		this.op = op;
		this.rhs = r;
	}
	
	public String toString() {
		return "(" + this.lhs + " " + this.op + " " + this.rhs + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
