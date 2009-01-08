package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;

public abstract class SugaredStatement {
	public final int sourceStart;
	
	public SugaredStatement(int sourceStart) {
		this.sourceStart = sourceStart;
	}
	public abstract String toString();
	public abstract SimpleStatement accept(DesugaringVisitor visitor);
	public abstract SugaredStatement accept(SimplifyingVisitor visitor);
	public abstract SugaredStatement accept(DesugarLoopVisitor visitor, /*@nullable*/SugaredStatement rest);
}
