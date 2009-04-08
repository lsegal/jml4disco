package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class ConstStatement extends Statement {
	private BoogieNode declaration;

	public ConstStatement(BoogieNode declaration, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.declaration = declaration;
	}
	
	public BoogieNode getDeclaration() {
		return declaration;
	}

	public void toBuffer(BoogieSource out) {
		out.append("const" + TOKEN_SPACE); //$NON-NLS-1$
		getDeclaration().toBuffer(out);
		out.appendLine(TOKEN_SEMICOLON);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			declaration.traverse(visitor);
		}
		visitor.endVisit(this);
	}

}