/**
 * 
 */
package org.jmlspecs.jml4.fspv.theory;

/**
 * @author karabot
 *
 */
public class TheoryAssignmentStatement extends TheoryStatement {
	
	public TheoryExpression	lhs;
	public TheoryExpression	rhs;

	public TheoryAssignmentStatement(TheoryExpression l, TheoryExpression r) {
		this.lhs = l;
		this.rhs = r;
	}

	public String toString() {
		return this.lhs + " = " + this.rhs; //$NON-NLS-1$
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
