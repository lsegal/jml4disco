package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class BinaryExpression extends Expression {
	private Expression left, right;
	private String operator;
	private boolean surroundWithParen;
	
	public BinaryExpression(Expression left, String operator, Expression right, ASTNode javaNode, Scope scope) {
		this(left, operator, right, true, javaNode, scope);
	}
	
	public BinaryExpression(Expression left, String operator, Expression right, boolean surroundWithParen, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.surroundWithParen = surroundWithParen;
		this.left = left;
		this.right = right;
		this.operator = operator;
	}

	public boolean isSurroundedWithParen() { 
		return surroundWithParen;
	}
	
	public Expression getLeft() { return left; }
	public Expression getRight() { return right; }
	public String getOperator() { return operator; }

	public void toBuffer(BoogieSource out) {
		if (isSurroundedWithParen()) out.append(TOKEN_LPAREN);
		getLeft().toBuffer(out);
		out.append(TOKEN_SPACE + getOperator() + TOKEN_SPACE); 
		getRight().toBuffer(out);
		if (isSurroundedWithParen()) out.append(TOKEN_RPAREN);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			getLeft().traverse(visitor);
			getRight().traverse(visitor);
		}
		visitor.endVisit(this);
	}
}
