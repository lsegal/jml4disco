package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class Axiom extends Statement {
	private Expression expression;
	private String prefix;
	private ArrayList/*<VariableDeclaration>*/ arguments;
	
	public Axiom(Expression expression, String prefix, VariableDeclaration[] arguments, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.expression = expression;
		this.prefix = prefix;
		this.arguments = new ArrayList();
		if (arguments != null) {
			for (int i = 0; i < arguments.length; i++) {
				this.arguments.add(arguments[i]);
			}
		}
	}
	
	public String getPrefix() {
		return prefix;
	}
	
	public ArrayList getArguments() {
		return arguments;
	}
	
	public Expression getExpression() { 
		return expression;
	}

	public void toBuffer(BoogieSource out) {
		out.append("axiom" + TOKEN_SPACE, getExpression().getJavaNode()); //$NON-NLS-1$
		if (getPrefix() != null && getArguments() != null) {
			out.append(TOKEN_LPAREN + getPrefix() + TOKEN_SPACE);
			for (int i = 0; i < getArguments().size(); i++) {
				((VariableDeclaration)getArguments().get(i)).toBuffer(out);
				if (i < getArguments().size() - 1) {
					out.append(TOKEN_COMMA + TOKEN_SPACE);
				}
			}
			out.append(TOKEN_SPACE + TOKEN_COLON + TOKEN_COLON + TOKEN_SPACE);
			getExpression().toBuffer(out);
			out.append(TOKEN_RPAREN);
		}
		else {
			getExpression().toBuffer(out);
		}
		out.appendLine(TOKEN_SEMICOLON);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			getExpression().traverse(visitor);
		}
		visitor.endVisit(this);
	}
	
}
