package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

public class JmlAssertStatement extends JmlAssertOrAssumeStatement {

	public JmlAssertStatement(String lexeme, Expression exceptionArgument,
			Expression assertExpression, int startPosition) {
		super(lexeme, exceptionArgument, assertExpression, startPosition);
	}

	public JmlAssertStatement(String lexeme, Expression assertExpression, int startPosition) {
		super(lexeme, assertExpression, startPosition);
	}
	public void traverse(ASTVisitor visitor, BlockScope scope) {
		if (visitor.visit(this, scope)) {
			this.assertExpression.traverse(visitor, scope);
			if (this.exceptionArgument != null) {
				this.exceptionArgument.traverse(visitor, scope);
			}
		}
		visitor.endVisit(this, scope);
	}	
	// FIXME: override the printStatement method
}
