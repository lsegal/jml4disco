package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class UnaryExpression extends Expression {
	private String operator;
	private Expression expression;
	
	public UnaryExpression(Expression expression, String operator, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.expression = expression;
		this.operator = operator;
	}
	
	public String getOperator() {
		return operator;
	}
	
	public Expression getExpression() {
		return expression;
	}

	public void toBuffer(BoogieSource out) {
		out.append(getOperator());
		getExpression().toBuffer(out);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			getExpression().traverse(visitor);
		}
		visitor.endVisit(this);
	}

}
