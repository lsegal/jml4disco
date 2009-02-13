package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;

/** @deprecated */
public class JmlMemberFieldRef extends ASTNode {

	public final /*@nullable*/ char[] identifier;
	public final /*@nullable*/ JmlMapsMemberRefExpr array;
	public final JmlMapsMemberRefExpr member;
	//@ invariant (identifer == null) ^ (array == null) ;
	
	public JmlMemberFieldRef(char[] identifier, JmlMapsMemberRefExpr refExpr) {
		this.identifier = identifier;
		this.array = null;
		this.member = refExpr;
	}

	public JmlMemberFieldRef(JmlMapsMemberRefExpr array, /*@nullable*/ JmlMapsMemberRefExpr member) {
		this.identifier = null;
		this.array = array;
		this.member = member;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		if (this.identifier != null) {
			output.append(this.identifier);
		} else {
			this.array.print(indent, output);
		}
		return this.member.print(indent, output);
	}

}
