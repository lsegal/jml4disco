package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

public class JmlAssumeStatement extends JmlAssertOrAssumeStatement {

	public JmlAssumeStatement(String lexeme, Expression exceptionArgument,
			Expression assertExpression, int startPosition) {
		super(lexeme, exceptionArgument, assertExpression, startPosition);
	}

	public JmlAssumeStatement(String lexeme, Expression assertExpression, int startPosition) {
		super(lexeme, assertExpression, startPosition);
	}

	public StringBuffer printStatement(int tab, StringBuffer output) {
		printIndent(tab, output);
		// FIXME: store the lexeme for the keyword and append it instead
		output.append("assume "); //$NON-NLS-1$
		this.assertExpression.printExpression(0, output);
		if (this.exceptionArgument != null) {
			output.append(": "); //$NON-NLS-1$
			this.exceptionArgument.printExpression(0, output);
		}
		return output.append(';');
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
}
