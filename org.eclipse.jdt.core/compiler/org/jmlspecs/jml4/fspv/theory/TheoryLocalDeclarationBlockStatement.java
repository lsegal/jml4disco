package org.jmlspecs.jml4.fspv.theory;

public class TheoryLocalDeclarationBlockStatement extends TheoryBlockStatement {

	public final TheoryVariable variable;

	public TheoryLocalDeclarationBlockStatement(TheoryVariable variable, TheoryStatement [] statements) {
		super(statements);
		this.variable = variable;
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
