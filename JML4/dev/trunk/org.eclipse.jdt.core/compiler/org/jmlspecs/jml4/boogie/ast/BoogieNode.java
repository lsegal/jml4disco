package org.jmlspecs.jml4.boogie.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public abstract class BoogieNode {
	public static final String TOKEN_EMPTY = ""; //$NON-NLS-1$
	public static final String TOKEN_SPACE = " "; //$NON-NLS-1$
	public static final String TOKEN_TAB = "\t"; //$NON-NLS-1$
	public static final String TOKEN_NEWLINE = "\n"; //$NON-NLS-1$
	public static final String TOKEN_COMMA = ","; //$NON-NLS-1$
	public static final String TOKEN_EQUALS = "="; //$NON-NLS-1$
	public static final String TOKEN_COLON = ":"; //$NON-NLS-1$
	public static final String TOKEN_SEMICOLON = ";"; //$NON-NLS-1$
	public static final String TOKEN_LPAREN = "("; //$NON-NLS-1$
	public static final String TOKEN_RPAREN = ")"; //$NON-NLS-1$
	public static final String TOKEN_LBRACE = "{"; //$NON-NLS-1$
	public static final String TOKEN_RBRACE = "}"; //$NON-NLS-1$
	public static final String TOKEN_LBRACK = "["; //$NON-NLS-1$
	public static final String TOKEN_RBRACK = "]"; //$NON-NLS-1$
	public static final String TOKEN_REF = "$Ref"; //$NON-NLS-1$
	public static final String TOKEN_RESULT = "$r"; //$NON-NLS-1$
	public static final String TOKEN_TNAME = "$TName"; //$NON-NLS-1$
	
	private ASTNode javaNode;
	private Scope scope;
	
	public BoogieNode(ASTNode javaNode, Scope scope) {
		this.javaNode = javaNode;
		this.scope = scope;
	}
	
	public Scope getScope() {
		return scope;
	}
	
	public ASTNode getJavaNode() {
		return javaNode;
	}
	
	public abstract void toBuffer(BoogieSource out);
	public abstract void traverse(Visitor visitor);
}
