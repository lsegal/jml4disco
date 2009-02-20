package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryEqualExpression extends TheoryBinaryExpression {

	public TheoryEqualExpression(ASTNode base, Theory theory, TheoryExpression left, TheoryExpression right) {
		super(base, theory, left, right);
	}
}
