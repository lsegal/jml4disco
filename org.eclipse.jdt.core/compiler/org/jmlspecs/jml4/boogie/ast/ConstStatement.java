package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class ConstStatement extends Statement {
	private TypeDeclaration declaration;

	public ConstStatement(TypeDeclaration declaration, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.declaration = declaration;
	}
	
	public TypeDeclaration getDeclaration() {
		return declaration;
	}

	public void toBuffer(BoogieSource out) {
		out.append("const" + TOKEN_SPACE + getDeclaration().getType().getTypeName()); //$NON-NLS-1$
		out.appendLine(TOKEN_COLON + TOKEN_SPACE + TOKEN_TNAME + TOKEN_SEMICOLON);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			declaration.traverse(visitor);
		}
		visitor.endVisit(this);
	}

}