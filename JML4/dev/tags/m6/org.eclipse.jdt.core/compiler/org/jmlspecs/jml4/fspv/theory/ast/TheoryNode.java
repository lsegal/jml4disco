package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public abstract class TheoryNode {

	public final ASTNode base;
	public final Theory enclosingTheory;
	
	public TheoryNode(ASTNode base, Theory theory) {
		this.base = base;
		this.enclosingTheory = theory;
	}
	
	public String toString() {
		return this.base.toString();
	}
	
	public abstract void traverse(TheoryVisitor visitor);
	
}
