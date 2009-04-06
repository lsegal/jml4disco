package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class FunctionDeclaration extends Statement {
	private String name;
	private ArrayList/*<VariableDeclaration>*/ arguments;
	private TypeReference returnType;
	private Expression expression;
	
	public FunctionDeclaration(String name, Expression expression, TypeReference returnType, VariableDeclaration[] arguments, ASTNode javaNode, Program scope) {
		super(javaNode, scope);
		this.returnType = returnType;
		this.name = name;
		this.expression = expression;
		this.arguments = new ArrayList();
		if (arguments != null) {
			for (int i = 0; i < arguments.length; i++) {
				this.arguments.add(arguments[i]);
			}
		}
	}

	public TypeReference getReturnType() {
		return returnType;
	}
	
	public ArrayList getArguments() {
		return arguments;
	}

	public Expression getExpression() {
		return expression;
	}
	
	public String getName() {
		return name;
	}
	
	private void printArguments(BoogieSource out) {
		out.append(TOKEN_LPAREN);
		for (int i = 0; i < getArguments().size(); i++) {
			((VariableDeclaration)getArguments().get(i)).toBuffer(out);
			if (i < getArguments().size() - 1) {
				out.append(TOKEN_COMMA + TOKEN_SPACE);
			}
		}
		out.append(TOKEN_RPAREN);
	}
	private void printReturns(BoogieSource out) {
		if (getReturnType() == null) return;
		out.append(TOKEN_SPACE);
		out.append("returns" + TOKEN_SPACE + TOKEN_LPAREN); //$NON-NLS-1$
		getReturnType().toBuffer(out);
		out.append(TOKEN_RPAREN);
	}
	
	private void printExpression(BoogieSource out) {
		if (getExpression() == null) return;
		out.append(TOKEN_SPACE + TOKEN_LBRACE + TOKEN_SPACE);
		getExpression().toBuffer(out);
		out.append(TOKEN_SPACE + TOKEN_RBRACE + TOKEN_SPACE);
	}
	
	public void toBuffer(BoogieSource out) {
		out.append("function" + TOKEN_SPACE + getName()); //$NON-NLS-1$
		printArguments(out);
		printReturns(out);
		printExpression(out);
		out.appendLine(getExpression() == null ? TOKEN_SEMICOLON : TOKEN_EMPTY);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			for (int i = 0; i < getArguments().size(); i++) {
				((BoogieNode)getArguments().get(i)).traverse(visitor);
			}
			if (getReturnType() != null) {
				getReturnType().traverse(visitor);
			}
			if (getExpression() != null) {
				getExpression().traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

}
