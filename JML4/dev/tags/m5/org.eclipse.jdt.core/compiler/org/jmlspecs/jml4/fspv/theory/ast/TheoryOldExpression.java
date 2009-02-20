package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryOldExpression extends TheoryUnaryExpression {

	public TheoryOldExpression(ASTNode base, Theory theory, TheoryExpression expression) {
		super(base, theory, expression);
		// TODO Auto-generated constructor stub
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
