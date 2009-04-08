package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class WhileStatement extends Statement {
	private ArrayList/*<Statement>*/ statements;
	private ArrayList/*<Expression>*/ invariants;
	private Expression condition;
	
	public WhileStatement(Expression condition, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.condition = condition;
		this.statements = new ArrayList();
		this.invariants = new ArrayList();
	}
	
	public ArrayList getStatements() {
		return statements;
	}
	
	public ArrayList getInvariants() {
		return invariants;
	}
	
	public Expression getCondition() {
		return condition;
	}

	public void toBuffer(BoogieSource out) {
		out.append("while" + TOKEN_SPACE); //$NON-NLS-1$
		if (getCondition() instanceof BinaryExpression) {
			getCondition().toBuffer(out);
		}
		else {
			out.append(TOKEN_LPAREN);
			getCondition().toBuffer(out);
			out.append(TOKEN_RPAREN);
		}
		if (getInvariants().size() > 0) {
			out.append(TOKEN_SPACE);
		}
		for (int i = 0; i < getInvariants().size(); i++) {
			Expression invariant = (Expression)getInvariants().get(i);
			out.append("invariant" + TOKEN_SPACE, invariant.getJavaNode()); //$NON-NLS-1$
			invariant.toBuffer(out);
			out.append(TOKEN_SEMICOLON);
		}
			
		out.appendLine(TOKEN_SPACE + TOKEN_LBRACE);
		out.increaseIndent();
		for (int i = 0; i < getStatements().size(); i++) {
			((Statement)getStatements().get(i)).toBuffer(out);
		}
		out.decreaseIndent();
		out.appendLine(TOKEN_RBRACE);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			condition.traverse(visitor);
			for (int i = 0; i < getStatements().size(); i++) {
				((Statement)getStatements().get(i)).traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

}
