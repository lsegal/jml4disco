package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public abstract class TheoryUnaryExpression extends TheoryExpression {

	public final TheoryExpression expression;

	public TheoryUnaryExpression(ASTNode base, Theory theory, TheoryExpression expression) {
		super(base, theory);
		this.expression = expression;
	}

}
