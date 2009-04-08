package org.jmlspecs.jml4.boogie.ast;

import org.jmlspecs.jml4.boogie.BoogieSource;

public class TokenLiteral extends Expression {
	private String literal;
	
	public TokenLiteral(String literal) {
		super(null, null);
		this.literal = literal; 
	}
	
	public String getLiteral() {
		return literal;
	}
	
	public void toBuffer(BoogieSource out) {
		out.append(getLiteral());
	}

	public void traverse(Visitor visitor) {
		// nothing
	}
}
