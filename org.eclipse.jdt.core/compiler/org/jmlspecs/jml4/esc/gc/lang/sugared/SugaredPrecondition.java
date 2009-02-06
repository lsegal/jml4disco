package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredOperator;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredPrecondition extends SugaredStatement {

	public final SugaredExpression pred;
	
	public SugaredPrecondition(SugaredExpression pred, SugaredExpression invariant, int sourceStart) {
		super(sourceStart);
		Utils.assertNotNull(pred, "pred is null"); //$NON-NLS-1$
		Utils.assertNotNull(invariant, "invariant is null"); //$NON-NLS-1$
		this.pred = new SugaredBinaryExpression(SugaredOperator.AND, invariant, pred, TypeBinding.BOOLEAN, sourceStart, pred.sourceEnd);
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
		return "[SugaredPrecondition: "+this.pred.toString()+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
