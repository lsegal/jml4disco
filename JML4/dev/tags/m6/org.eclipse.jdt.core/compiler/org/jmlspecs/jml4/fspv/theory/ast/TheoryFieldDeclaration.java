package org.jmlspecs.jml4.fspv.theory.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.TypeIds;

public class TheoryFieldDeclaration extends TheoryVariableDeclaration {

	public final TheoryExpression initialization;

	public TheoryFieldDeclaration(ASTNode base, Theory theory, TheoryExpression initialization) {
		super(base, theory);
		this.initialization = initialization;
	}

	public void traverse(TheoryVisitor visitor) {
		if(visitor.visit(this)) {
			if(this.initialization != null) {
				this.initialization.traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

	public boolean isStatic() {
		FieldDeclaration fieldDeclaration = (FieldDeclaration) this.base;
		return fieldDeclaration.isStatic();
	}

	public boolean isBaseType() {
		FieldDeclaration fieldDeclaration = (FieldDeclaration) this.base;
		return fieldDeclaration.binding.type.isBaseType();
	}

	public boolean isArrayType() {
		FieldDeclaration fieldDeclaration = (FieldDeclaration) this.base;
		return fieldDeclaration.binding.type.isArrayType();
	}

	public boolean isClassType() {
		FieldDeclaration fieldDeclaration = (FieldDeclaration) this.base;
		return fieldDeclaration.binding.type.isClass();
	}

	public boolean isIntType() {
		FieldDeclaration fieldDeclaration = (FieldDeclaration) this.base;
		return this.isBaseType() && fieldDeclaration.binding.type.id == TypeIds.T_int;
	}
	
	public boolean isBooleanType() {
		FieldDeclaration fieldDeclaration = (FieldDeclaration) this.base;
		return this.isBaseType() && fieldDeclaration.binding.type.id == TypeIds.T_boolean;
	}
	
	public String getName() {
		FieldDeclaration fieldDeclaration = (FieldDeclaration) this.base;
		return new String(fieldDeclaration.name);
	}
	
	public String getType() {
		FieldDeclaration fieldDeclaration = (FieldDeclaration) this.base;
		return fieldDeclaration.type.toString();
	}
	
}
