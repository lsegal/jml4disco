package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryAllocationExpression extends TheoryExpression {

	public final TheoryExpression[] arguments;

	public TheoryAllocationExpression(ASTNode base, Theory theory, TheoryExpression[] arguments) {
		super(base, theory);
		this.arguments = arguments;
	}

	public void traverse(TheoryVisitor visitor) {
		if(visitor.visit(this)){
			if(this.arguments != null) {
				for(int i=0;i<this.arguments.length;i++)
					this.arguments[i].traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

}
