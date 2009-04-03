package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class IntLiteral extends Expression {
	private int value;
	
	public IntLiteral(int value, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.value = value;
	}
	
	public int getValue() {
		return value;
	}

	public void toBuffer(BoogieSource out) {
		out.append(String.valueOf(getValue()), getJavaNode());
	}

	public void traverse(Visitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}

}
