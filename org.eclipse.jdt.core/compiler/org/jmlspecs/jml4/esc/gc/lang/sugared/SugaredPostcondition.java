package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredOperator;

public class SugaredPostcondition extends SugaredStatement {

	public final SugaredExpression pred;
	public final int methodStart; 

	public SugaredPostcondition(SugaredExpression pred, SugaredExpression invariant, int sourceStart, int methodStart) {
		super(sourceStart);
		this.pred = new SugaredBinaryExpression(SugaredOperator.AND, invariant, pred, TypeBinding.BOOLEAN, sourceStart, pred.sourceEnd);
		this.methodStart = methodStart;
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
		return "[SugaredPostcondition: "+this.pred.toString()+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
