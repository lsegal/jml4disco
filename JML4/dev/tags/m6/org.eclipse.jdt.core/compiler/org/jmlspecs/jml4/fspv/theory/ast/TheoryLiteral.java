package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public abstract class TheoryLiteral extends TheoryExpression {

	public TheoryLiteral(ASTNode base, Theory theory) {
		super(base, theory);
	}

}
