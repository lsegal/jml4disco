package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredVariable;

public class SugaredHavoc extends SugaredStatement {
	public final SugaredVariable var;

	public SugaredHavoc(SugaredVariable var, int sourceStart) {
		super(sourceStart);
		this.var = var;
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
		return "[SugaredHavoc: "+this.var.toString()+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
