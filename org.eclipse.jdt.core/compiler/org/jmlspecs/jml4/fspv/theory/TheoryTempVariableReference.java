package org.jmlspecs.jml4.fspv.theory;


public class TheoryTempVariableReference extends TheoryVariableReference {

	public final int incarnation;

	public TheoryTempVariableReference(TheoryVariableReference v, int i) {
		super(v.variable);
		this.incarnation = i;
	}

	public String toString() {
		return this.variable.getDecoratedName()+this.incarnation;
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
