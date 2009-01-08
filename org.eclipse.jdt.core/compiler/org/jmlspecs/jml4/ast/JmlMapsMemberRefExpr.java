package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

public class JmlMapsMemberRefExpr extends ASTNode {

	public final               char[]    identifier;
	public final /*@nullable*/ JmlName[] dims;

	public JmlMapsMemberRefExpr(char[] identifier) {
		this.identifier = identifier;
		this.dims = null;
	}
	public JmlMapsMemberRefExpr(char[] identifier, JmlName[] dims) {
		this.identifier = identifier;
		this.dims = dims;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		output.append(this.identifier);
		int length = (this.dims == null ? 0 : this.dims.length);
		for (int i = 0; i < length; i++) {
			output.append('[');
			this.dims[i].print(indent, output);
			output.append(']');
		}
		return output;
	}

}
