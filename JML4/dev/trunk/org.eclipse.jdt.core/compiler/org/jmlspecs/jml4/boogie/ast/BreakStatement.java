package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class BreakStatement extends Statement {
	private String label;
	
	public BreakStatement(String label, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.label = label;
	}
	
	public String getLabel() {
		return label;
	}
	
	public void toBuffer(BoogieSource out) {
		out.append("break", getJavaNode()); //$NON-NLS-1$
		if (getLabel() != null) {
			out.append(TOKEN_SPACE + getLabel());
		}
		out.appendLine(TOKEN_SEMICOLON);
	}

	public void traverse(Visitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}

}
