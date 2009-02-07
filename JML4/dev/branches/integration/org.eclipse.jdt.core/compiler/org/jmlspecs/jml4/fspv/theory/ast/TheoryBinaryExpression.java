package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryBinaryExpression extends TheoryExpression implements TheoryOperatorIds {

	public final TheoryExpression left;
	public final TheoryExpression expression;

	public TheoryBinaryExpression(ASTNode base, Theory theory, TheoryExpression left, TheoryExpression expression) {
		super(base, theory);
		this.left = left;
		this.expression = expression;
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
