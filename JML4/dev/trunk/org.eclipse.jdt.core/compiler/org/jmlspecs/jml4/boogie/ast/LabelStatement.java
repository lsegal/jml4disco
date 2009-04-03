package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class LabelStatement extends Statement {
	private String labelName;

	public LabelStatement(String labelName, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.labelName = labelName;
	}
	
	public String getLabelName() {
		return labelName;
	}

	public void toBuffer(BoogieSource out) {
		out.appendLine(getLabelName() + TOKEN_COLON);
	}

	public void traverse(Visitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}
	
}
