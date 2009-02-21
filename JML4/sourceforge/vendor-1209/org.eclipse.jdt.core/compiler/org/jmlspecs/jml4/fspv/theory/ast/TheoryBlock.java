package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryBlock extends TheoryStatement {

	public final TheoryStatement[] statements;

	public TheoryBlock(ASTNode base, Theory theory, TheoryStatement[] statements) {
		super(base, theory);
		this.statements = statements;
	}

	public void traverse(TheoryVisitor visitor) {
		if(visitor.visit(this)) {
			for(int i=0;i<this.statements.length;i++)
				this.statements[i].traverse(visitor);
		}
		visitor.endVisit(this);
	}
	
	
}
