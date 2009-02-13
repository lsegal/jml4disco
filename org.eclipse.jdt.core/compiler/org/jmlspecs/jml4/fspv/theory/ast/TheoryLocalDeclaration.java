package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;

public class TheoryLocalDeclaration extends TheoryVariableDeclaration {

	public final TheoryExpression initialization;

	public TheoryLocalDeclaration(ASTNode base, Theory theory, TheoryExpression initialization) {
		super(base, theory);
		this.initialization = initialization;
	}

	public String getName() {
		LocalDeclaration localDeclaration = (LocalDeclaration) this.base;
		return new String(localDeclaration.name);
	}

	public String getType() {
		LocalDeclaration localDeclaration = (LocalDeclaration) this.base;
		return localDeclaration.type.toString();
	}
	
	public void traverse(TheoryVisitor visitor) {
		// TODO Auto-generated method stub
		if(visitor.visit(this)) {
			if(this.initialization != null) {
				this.initialization.traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}	

}
