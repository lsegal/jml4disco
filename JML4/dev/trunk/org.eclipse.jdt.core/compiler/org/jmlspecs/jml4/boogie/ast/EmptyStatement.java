package org.jmlspecs.jml4.boogie.ast;

import org.jmlspecs.jml4.boogie.BoogieSource;

public class EmptyStatement extends Statement {
	public EmptyStatement() {
		super(null, null);
	}

	public void toBuffer(BoogieSource out) {
		// does nothing

	}

	public void traverse(Visitor visitor) {
		// does nothing
	}
}
