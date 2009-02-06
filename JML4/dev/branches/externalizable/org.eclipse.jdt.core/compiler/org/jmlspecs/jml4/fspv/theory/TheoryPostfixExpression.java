package org.jmlspecs.jml4.fspv.theory;

public class TheoryPostfixExpression extends TheorySideEffectExpression {

	public final TheoryAssignmentStatement assignment;

	public TheoryPostfixExpression(TheoryAssignmentStatement a) {
		super(a.lhs.type);
		this.assignment = a;
	}

	public String toString() {
		return assignment.lhs.toString();
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
