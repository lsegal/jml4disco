package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class WhileStatement extends Statement {
	private ArrayList/*<Statement>*/ statements;
	private Expression condition;
	
	public WhileStatement(Expression condition, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.condition = condition;
		this.statements = new ArrayList();
	}
	
	public ArrayList getStatements() {
		return statements;
	}
	
	public Expression getCondition() {
		return condition;
	}

	public void toBuffer(BoogieSource out) {
		out.append("while" + TOKEN_SPACE); //$NON-NLS-1$
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
