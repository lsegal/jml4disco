package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public abstract class TheoryVariableDeclaration extends TheoryStatement {

	public TheoryVariableDeclaration(ASTNode base, Theory theory) {
		super(base, theory);
		// TODO Auto-generated constructor stub
	}

	public abstract String getType();
	
	public abstract String getName();

}
