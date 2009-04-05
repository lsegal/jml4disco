package org.jmlspecs.jml4.boogie.ast;

import org.jmlspecs.jml4.boogie.BoogieSource;

public class VariableDeclaration extends BoogieNode {
	private VariableReference name;
	private TypeReference type;
	private String shortName;
	private boolean constant;
	private boolean unique;
	
	public VariableDeclaration(VariableReference name, TypeReference type, Scope scope) {
		this(name, type, false, scope);
	}
	
	public VariableDeclaration(VariableReference name, TypeReference type, boolean constant, Scope scope) {
		super(null, scope);
		this.type = type;
		this.name = name;
		this.shortName = null;
		this.constant = constant;
		this.unique = false;
	}
	
	public boolean isConstant() {
		return constant;
	}
	
	public boolean isUnique() {
		return unique;
	}
	
	public void setUnique(boolean unique) {
		this.unique = unique;
	}

	public VariableReference getName() {
		return name;
	}
	
	public TypeReference getType() {
		return type;
	}
	
	public String getShortName() {
		return shortName;
	}
	
	public void setShortName(String shortName) {
		this.shortName = shortName;
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
