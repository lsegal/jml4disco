package org.jmlspecs.jml4.boogie.ast;

import org.jmlspecs.jml4.boogie.BoogieSource;

public class Comment extends Statement {
	private String comment;

	public Comment(String comment) {
		super(null, null);
		this.comment = comment;
	}
	
	public String getComment() {
		return comment;
	}
	
	public void toBuffer(BoogieSource out) {
		out.appendLine(getComment());
	}

	public void traverse(Visitor visitor) {
		// nothing
	}
}
