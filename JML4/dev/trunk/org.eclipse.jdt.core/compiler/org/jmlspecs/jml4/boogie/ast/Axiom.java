package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class Axiom extends Statement {
	private Expression expression;
	
	public Axiom(Expression expression, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.expression = expression;
	}
	
	public Expression getExpression() { 
		return expression;
	}

	public void toBuffer(BoogieSource out) {
		out.append("axiom" + TOKEN_SPACE, getExpression().getJavaNode()); //$NON-NLS-1$
		getExpression().toBuffer(out);
		out.appendLine(TOKEN_SEMICOLON);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			getExpression().traverse(visitor);
		}
		visitor.endVisit(this);
	}
	
}
