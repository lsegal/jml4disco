package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredAssume extends SugaredStatement {
	public final SugaredExpression pred;

	public SugaredAssume(SugaredExpression pred, int sourceStart) {
		super(sourceStart);
		Utils.assertTrue(pred.type == TypeBinding.BOOLEAN, "pred is not a boolean but a '"+pred.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		this.pred = pred;
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
		return "[SugaredAssume: "+this.pred.toString()+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
