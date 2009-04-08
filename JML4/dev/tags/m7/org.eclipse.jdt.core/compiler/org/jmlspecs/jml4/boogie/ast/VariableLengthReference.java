package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class VariableLengthReference extends VariableReference {
	public VariableLengthReference(String name, ASTNode javaNode, Scope scope) {
		super(name, javaNode, scope);
	}

	public void toBuffer(BoogieSource out) {
		super.toBuffer(out);
		out.append(".length"); //$NON-NLS-1$
	}	
}
