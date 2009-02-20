package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class TheoryWhileStatement extends TheoryStatement {

	public final TheoryExpression condition;
	public final TheoryStatement action;
	public final TheoryExpression[] invariants;
	public final TheoryExpression[] variants;
	public TheoryWhileStatement(ASTNode base, Theory theory,
			TheoryExpression condition, TheoryStatement action, 
			TheoryExpression[] invariants, TheoryExpression[] variants) {
		super(base, theory);
		this.condition = condition;
		this.action = action;
		this.invariants = invariants;
		this.variants = variants;
	}

	public void traverse(TheoryVisitor visitor) {
		if(visitor.visit(this)) {
			if(this.condition != null) {
				this.condition.traverse(visitor);
			}
			if(this.action != null) {
				this.action.traverse(visitor);
			}
			if(this.invariants != null) {
				for(int i=0;i<this.invariants.length;i++)
					this.invariants[i].traverse(visitor);
			}
			if(this.variants != null) {
				for(int i=0;i<this.variants.length;i++)
					this.variants[i].traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

}
