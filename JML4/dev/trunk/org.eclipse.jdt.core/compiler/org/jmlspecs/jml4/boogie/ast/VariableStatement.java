package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class VariableStatement extends Statement {
	private VariableDeclaration declaration;

	public VariableStatement(VariableDeclaration declaration, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.declaration = declaration;
	}
	
	public VariableDeclaration getDeclaration() {
		return declaration;
	}

	public void toBuffer(BoogieSource out) {
		out.append((getDeclaration().isConstant() ? "const" : "var") + TOKEN_SPACE); //$NON-NLS-1$ //$NON-NLS-2$
		if (getDeclaration().isUnique()) out.append("unique" + TOKEN_SPACE); //$NON-NLS-1$
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
