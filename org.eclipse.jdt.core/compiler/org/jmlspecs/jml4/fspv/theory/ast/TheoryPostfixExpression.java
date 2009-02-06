package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryPostfixExpression extends TheoryCompoundAssignment{
	
	public TheoryPostfixExpression(ASTNode base, Theory theory, TheoryExpression left) {
		super(base, theory, left, null);
	}
	
	public void traverse(TheoryVisitor visitor) {
		if(visitor.visit(this)) {
			if(this.left != null) {
				this.left.traverse(visitor);
			}
			if(this.expression != null) {
				this.expression.traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

}
