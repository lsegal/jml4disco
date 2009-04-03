package org.jmlspecs.jml4.boogie.ast;

import org.jmlspecs.jml4.boogie.BoogieSource;

public class TypeDeclaration extends BoogieNode {
	private TypeReference type;
	private TypeReference superType;
	
	public TypeDeclaration(TypeReference type, TypeReference superType, Scope scope) {
		super(null, scope);
		this.type = type;
		this.superType = superType;
	}
	
	public TypeReference getType() {
		return type;
	}
	
	public TypeReference getSuperType() {
		return superType;
	}

	public void toBuffer(BoogieSource out) {
		return;
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			type.traverse(visitor);
			superType.traverse(visitor);
		}
		visitor.endVisit(this);
	}


}
