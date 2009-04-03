package org.jmlspecs.jml4.boogie.ast;

import org.jmlspecs.jml4.boogie.BoogieSource;

public class VariableDeclaration extends BoogieNode {
	private VariableReference name;
	private TypeReference type;
	
	public VariableDeclaration(VariableReference name, TypeReference type, Scope scope) {
		super(null, scope);
		this.type = type;
		this.name = name;
	}
	
	public VariableReference getName() {
		return name;
	}
	
	public TypeReference getType() {
		return type;
	}
	
	public boolean isLocal() {
		return getScope() instanceof Procedure;
	}

	public void toBuffer(BoogieSource out) {
		getName().toBuffer(out);
		out.append(TOKEN_COLON + TOKEN_SPACE);
		getType().toBuffer(out);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			name.traverse(visitor);
			type.traverse(visitor);
		}
		visitor.endVisit(this);
	}

}
