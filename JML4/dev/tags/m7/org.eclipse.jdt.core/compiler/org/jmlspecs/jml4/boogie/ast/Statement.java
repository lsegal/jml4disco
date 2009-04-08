package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public abstract class Statement extends BoogieNode {
	public Statement(ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
	}
}
