package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;

public class TheoryCompoundAssignment extends TheoryAssignment implements TheoryOperatorIds {

	public TheoryCompoundAssignment(ASTNode base, Theory theory, TheoryExpression left, TheoryExpression expression) {
		super(base, theory, left, expression);
	}
	
	public TheoryExpression getExpression() {
		TheoryBinaryExpression binExpr = (TheoryBinaryExpression) this.expression;
		return binExpr.expression;
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

	public int getOperator() {
		CompoundAssignment e = (CompoundAssignment) this.base;
		return (e.bits & ASTNode.OperatorMASK) >> ASTNode.OperatorSHIFT;
	}
	
}
