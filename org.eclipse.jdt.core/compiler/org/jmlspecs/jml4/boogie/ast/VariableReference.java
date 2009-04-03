package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class VariableReference extends Expression {
	private String name;
	
	public VariableReference(String name, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.name = name;
	}
	
	public String getName() {
		return name;
	}

	public void toBuffer(BoogieSource out) {
		out.append(getName(), getJavaNode());
	}

	public void traverse(Visitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}
}
