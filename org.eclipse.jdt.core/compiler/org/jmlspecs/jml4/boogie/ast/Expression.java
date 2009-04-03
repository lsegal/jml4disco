package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public abstract class Expression extends BoogieNode {
	public Expression(ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
	}
}
