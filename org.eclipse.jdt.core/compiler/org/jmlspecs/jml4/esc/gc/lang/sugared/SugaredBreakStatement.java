package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredBreakStatement extends SugaredStatement {

	public final String label;

	public SugaredBreakStatement(String label, int sourceStart) {
		super(sourceStart);
		Utils.assertNotNull(label, "label must not be null"); //$NON-NLS-1$
		Utils.assertTrue(label.indexOf("break") >= 0, "break label is "+label); //$NON-NLS-1$ //$NON-NLS-2$

		this.label = label;
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
		return "[SugaredBreak: "+this.label+"]";  //$NON-NLS-1$//$NON-NLS-2$
	}
}
