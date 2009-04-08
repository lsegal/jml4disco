package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class AssumeStatement extends Statement {
	private Expression expression;

	public AssumeStatement(Expression expression, ASTNode javaNode, Procedure scope) {
		super(javaNode, scope);
		this.expression = expression;
	}
	
	public Expression getExpression() {
		return expression;
	}

	public void toBuffer(BoogieSource out) {
		out.append("assume" + TOKEN_SPACE, expression.getJavaNode()); //$NON-NLS-1$
		getExpression().toBuffer(out);
		out.appendLine(TOKEN_SEMICOLON);
	}

	public void traverse() {
		// TODO Auto-generated method stub
		
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			getExpression().traverse(visitor);
		}
		visitor.endVisit(this);
	}

}
