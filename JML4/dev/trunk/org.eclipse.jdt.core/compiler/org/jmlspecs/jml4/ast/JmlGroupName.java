package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

/** @deprecated */
public class JmlGroupName extends ASTNode {

	static class Prefix {
		String s;
		Prefix(String s) {this.s = s;}
	}
	public static final Prefix This = new Prefix("this"); //$NON-NLS-1$
	public static final Prefix Super = new Prefix("super"); //$NON-NLS-1$
	public static final Prefix None = new Prefix(null);

	public final char[] identifier;
	public final Object prefix;

	public JmlGroupName(char[] identifier) {
		this.identifier = identifier;
		this.prefix = None;
	}
	public JmlGroupName(Prefix prefix, char[] identifier) {
		this.identifier = identifier;
		this.prefix = prefix;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		if (this.prefix != None)
			output.append(this.prefix).append('.');
		return output.append(this.identifier);
	}
	
}
