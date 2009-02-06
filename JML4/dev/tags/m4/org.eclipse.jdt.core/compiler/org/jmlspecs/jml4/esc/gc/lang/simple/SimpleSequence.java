package org.jmlspecs.jml4.esc.gc.lang.simple;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleSequence extends SimpleStatement {

	public final SimpleStatement stmt1;
	private      SimpleStatement stmt2;

	public SimpleSequence(SimpleStatement stmt1, SimpleStatement stmt2) {
		super(stmt1.sourceStart);
		this.stmt1 = stmt1;
		this.stmt2 = stmt2;
		Utils.assertTrue(! (this.stmt1 instanceof SimpleGoto), "stmt1 is a go goto statements"); //$NON-NLS-1$
		SimpleStatement theStmt= stmt1;
		while (theStmt instanceof SimpleSequence)
			theStmt = ((SimpleSequence)theStmt).stmt2;
		Utils.assertTrue(! (theStmt instanceof SimpleGoto), "stmt1 has an embedded goto statement"); //$NON-NLS-1$
	}

	public CfgStatement accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		Utils.assertTrue(! (this.stmt1 instanceof SimpleGoto), "too many goto statements"); //$NON-NLS-1$
		return visitor.visit(this, incarnationMap);
	}

	public String toString() {
		return "[SimpleSequence:\n\t\t" +  //$NON-NLS-1$
			   this.stmt1 + "\n\t\t" +  //$NON-NLS-1$
			   this.stmt2 + "]"; //$NON-NLS-1$
	}

	public SimpleStatement stmt2() {
		return this.stmt2;
	}
	/*package*/ void setStmt2(SimpleStatement stmt) {
		Utils.assertTrue((stmt instanceof SimpleGoto
		   || (stmt instanceof SimpleSequence && ((SimpleSequence)stmt).stmt2() instanceof SimpleGoto)), 
		   "stmt is a "+stmt.getClass().getName()); //$NON-NLS-1$
		if (this.stmt2 instanceof SimpleGoto) {
			this.stmt2 = stmt;
		} else if (this.stmt2 instanceof SimpleSequence) {
			((SimpleSequence)this.stmt2).setStmt2(stmt);
		} else {
			this.stmt2 = new SimpleSequence(this.stmt2, stmt);
		}
	}

	public static SimpleStatement fold(SimpleStatement[] block) {
		if (block.length == 0) return SimpleAssert.SKIP;
		if (block.length == 1) return block[0];
		SimpleStatement result = block[block.length - 1];
		for(int i=block.length - 2; i>=0; i--) {
			result = new SimpleSequence(block[i], result);
		}
		return result;
	}

}
