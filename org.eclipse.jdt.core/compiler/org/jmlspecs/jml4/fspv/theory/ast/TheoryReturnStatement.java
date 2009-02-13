package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryReturnStatement extends TheoryStatement {

	public final TheoryExpression expression;

	public TheoryReturnStatement(ASTNode base, Theory theory, TheoryExpression expression) {
		super(base, theory);
		this.expression = expression;
	}

	public void traverse(TheoryVisitor visitor) {
		if(visitor.visit(this)) {
			if(this.expression != null) {
				this.expression.traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}
	
	

}
