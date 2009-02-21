package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredSequence extends SugaredStatement {

	public final SugaredStatement stmt1;
	private      SugaredStatement stmt2;

	public SugaredSequence(SugaredStatement stmt1, SugaredStatement stmt2) {
		super(stmt1.sourceStart);
		Utils.assertNotNull(stmt2, "stmt2 is null"); //$NON-NLS-1$
		Utils.assertTrue(! (stmt1 instanceof SugaredGoto), "stmt1 is a goto statement"); //$NON-NLS-1$
		SugaredStatement theStmt= stmt1;
		while (theStmt instanceof SugaredSequence)
			theStmt = ((SugaredSequence)theStmt).stmt2;
		Utils.assertTrue(! (theStmt instanceof SugaredGoto), "stmt1 has an embedded goto statement"); //$NON-NLS-1$

		this.stmt1 = stmt1;
		this.stmt2 = stmt2;
	}
	
	public SugaredStatement stmt2() {
		return this.stmt2;
	}
	/*package*/ void setStmt2(SugaredStatement stmt) {
		Utils.assertTrue(stmt instanceof SugaredGoto
		   || (stmt instanceof SugaredSequence && ((SugaredSequence)stmt).stmt2() instanceof SugaredGoto),
		   "stmt is a "+stmt.getClass().getName()); //$NON-NLS-1$
		if (this.stmt2 instanceof SugaredGoto) {
			this.stmt2 = stmt;
		} else if (this.stmt2 instanceof SugaredSequence) {
			((SugaredSequence)this.stmt2).setStmt2(stmt);
		} else {
			this.stmt2 = new SugaredSequence(this.stmt2, stmt);
		}
	}

	public SimpleStatement accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}
	public SugaredStatement accept(SimplifyingVisitor visitor) {
		return visitor.visit(this);
	}
	public SugaredStatement accept(DesugarLoopVisitor visitor, SugaredStatement rest) {
		return visitor.visit(this, rest);
	}
	public String toString() {
		return "[SugaredSequence:\n\t\t"+ //$NON-NLS-1$
			   this.stmt1.toString() + "\n\t\t" + //$NON-NLS-1$
		       this.stmt2.toString()+"]"; //$NON-NLS-1$
	}

	public static SugaredStatement fold(SugaredStatement[] block) {
		if (block.length == 0) return SugaredAssert.SKIP;
		if (block.length == 1) return block[0];
		SugaredStatement result = block[block.length - 1];
		for(int i=block.length - 2; i>=0; i--) {
			result = new SugaredSequence(block[i], result);
		}
		return result;
	}

	public boolean endsInGoto() {
		if (this.stmt2 instanceof SugaredGoto)
			return true;
		else if (this.stmt2 instanceof SugaredSequence)
			return ((SugaredSequence)this.stmt2).endsInGoto();
		else
			return false;
	}

	public /*@nullable*/ SugaredGoto getFinalGotos() {
		if (this.stmt2 instanceof SugaredGoto)
			return (SugaredGoto) this.stmt2;
		else if (this.stmt2 instanceof SugaredSequence)
			return ((SugaredSequence)this.stmt2).getFinalGotos();
		else
			return null;
	}
}
