package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Assignment;

public class TheoryAssignment extends TheoryExpression {

	public final TheoryExpression left;
	public final TheoryExpression expression;

	public TheoryAssignment(ASTNode base, Theory theory, TheoryExpression lhs, TheoryExpression expression) {
		super(base, theory);
		this.left = lhs;
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

	public boolean isSubExpression() {
		Assignment a = (Assignment) this.base;
		return a.statementEnd == -1;
	}

}
