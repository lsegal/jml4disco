package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.lookup.Binding;

public class TheorySingleNameReference extends TheoryReference {

	public TheorySingleNameReference(ASTNode base, Theory theory) {
		super(base, theory);
	}

	public void traverse(TheoryVisitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}

	public boolean isField() {
		return (this.base.bits & ASTNode.RestrictiveFlagMASK) == Binding.FIELD;
	}

	public boolean isLocal() {
		return (this.base.bits & ASTNode.RestrictiveFlagMASK) == Binding.LOCAL;
	}

	
}
