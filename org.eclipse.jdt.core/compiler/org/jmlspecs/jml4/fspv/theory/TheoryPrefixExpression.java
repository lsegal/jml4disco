package org.jmlspecs.jml4.fspv.theory;

public class TheoryPrefixExpression extends TheorySideEffectExpression {

	public final TheoryAssignmentStatement assignment;

	public TheoryPrefixExpression(TheoryAssignmentStatement a) {
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
