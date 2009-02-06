package org.jmlspecs.jml4.fspv.theory;

public class TheoryBindStatement extends TheoryStatement {

	public final TheoryTempVariableReference tempVariableReference;
	public final TheoryAssignmentStatement assignment;

	public TheoryBindStatement(TheoryTempVariableReference temp,
			TheoryAssignmentStatement assignment) {
		this.tempVariableReference = temp;
		this.assignment = assignment;
	}
	
	public String toString() {
		return this.tempVariableReference + " . " + this.assignment; //$NON-NLS-1$
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}


}
