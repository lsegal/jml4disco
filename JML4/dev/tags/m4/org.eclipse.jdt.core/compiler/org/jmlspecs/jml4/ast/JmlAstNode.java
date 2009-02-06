package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public abstract class JmlAstNode extends ASTNode {

	public final static String EMPTY_STRING = ""; //$NON-NLS-1$
	public final static String COMMA = ","; //$NON-NLS-1$
	public final static String SPACE = " "; //$NON-NLS-1$
	public final static String SEMICOLON = ";"; //$NON-NLS-1$
	
	public final static String THIS = "this"; //$NON-NLS-1$
	public final static String SUPER = "super"; //$NON-NLS-1$
	
	public JmlAstNode() {
		/* empty */
	}

}
