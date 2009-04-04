package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class IfStatement extends Statement {
	private ArrayList/*<Statement>*/ thenStatements;
	private ArrayList/*<Statement>*/ elseStatements;
	private Expression condition;
	
	public IfStatement(Expression condition, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.condition = condition;
		this.thenStatements = new ArrayList();
		this.elseStatements = new ArrayList();
	}
	
	public ArrayList getThenStatements() {
		return thenStatements;
	}
	
	public ArrayList getElseStatements() {
		return elseStatements;
	}

	public Expression getCondition() {
		return condition;
	}

	public void toBuffer(BoogieSource out) {
		out.append("if" + TOKEN_SPACE); //$NON-NLS-1$
		if (getCondition() instanceof BinaryExpression) {
			out.append(TOKEN_LPAREN);
			getCondition().toBuffer(out);
			out.append(TOKEN_RPAREN);
		}
		else {
			getCondition().toBuffer(out);
		}

		out.appendLine(TOKEN_SPACE + TOKEN_LBRACE);
		out.increaseIndent();
		for (int i = 0; i < getThenStatements().size(); i++) {
			((Statement)getThenStatements().get(i)).toBuffer(out);
		}
		out.decreaseIndent();
		out.appendLine(TOKEN_RBRACE);
		if (getElseStatements().size() > 0) {
			out.appendLine("else" + TOKEN_SPACE + TOKEN_LBRACE); //$NON-NLS-1$
			out.increaseIndent();
			for (int i = 0; i < getElseStatements().size(); i++) {
				((Statement)getElseStatements().get(i)).toBuffer(out);
			}
			out.decreaseIndent();
			out.appendLine(TOKEN_RBRACE);
		}
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			getCondition().traverse(visitor);
			for (int i = 0; i < getThenStatements().size(); i++) {
				((BoogieNode)getThenStatements().get(i)).traverse(visitor);
			}
			for (int i = 0; i < getElseStatements().size(); i++) {
				((BoogieNode)getElseStatements().get(i)).traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

}
