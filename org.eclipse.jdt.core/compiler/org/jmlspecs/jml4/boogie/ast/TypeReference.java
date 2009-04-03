package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class TypeReference extends Expression {
	private String typeName;
	
	public TypeReference(String typeName, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.typeName = typeName;
	}
	
	public String getTypeName() {
		return typeName;
	}

	public void toBuffer(BoogieSource out) {
		out.append(isNative() ? getTypeName() : TOKEN_REF, getJavaNode());
	}
	
	public boolean isNative() {
		String nativeTypes[] = { "int", "bool", "long", "char", "double", "float" }; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$//$NON-NLS-4$//$NON-NLS-5$ //$NON-NLS-6$
		for (int i = 0; i < nativeTypes.length; i++) {
			if (getTypeName().equals(nativeTypes[i])) return true;
		}
		return false;
	}

	public void traverse(Visitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}

}
