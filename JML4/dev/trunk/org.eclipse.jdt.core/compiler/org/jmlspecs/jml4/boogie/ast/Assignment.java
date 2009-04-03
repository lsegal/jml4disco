package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class Assignment extends Statement {
	private VariableReference variable;
	private Expression expression;
	
	public Assignment(VariableReference lhs, Expression rhs, ASTNode javaNode, Procedure scope) {
		super(javaNode, scope);
		this.variable = lhs;
		this.expression = rhs;
	}
	
	public VariableReference getVariable() {
		return variable;
	}
	
	public Expression getExpression() {
		return expression;
	}

	public void toBuffer(BoogieSource out) {
		getVariable().toBuffer(out);
		out.append(TOKEN_SPACE);
		out.append(TOKEN_COLON + TOKEN_EQUALS + TOKEN_SPACE, getVariable().getJavaNode());
		getExpression().toBuffer(out);
		out.appendLine(TOKEN_SEMICOLON);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			getVariable().traverse(visitor);
			getExpression().traverse(visitor);
		}
		visitor.endVisit(this);
	}

}
