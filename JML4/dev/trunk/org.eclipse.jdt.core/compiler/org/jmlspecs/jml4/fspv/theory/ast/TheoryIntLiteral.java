package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryIntLiteral extends TheoryLiteral {

	public TheoryIntLiteral(ASTNode base, Theory theory) {
		super(base, theory);
	}

	public void traverse(TheoryVisitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}

}
