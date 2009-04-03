package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class ReturnStatement extends Statement {
	public ReturnStatement(ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
	}
	
	public void toBuffer(BoogieSource out) {
		out.append("return", getJavaNode()); //$NON-NLS-1$
		out.appendLine(TOKEN_SEMICOLON);
	}

	public void traverse(Visitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}
}
