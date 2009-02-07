package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryResultReference extends TheoryReference {

	public TheoryResultReference(ASTNode base, Theory theory) {
		super(base, theory);
		// TODO Auto-generated constructor stub
	}

	public void traverse(TheoryVisitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}

}
