package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public class SugaredOldExpression extends SugaredExpression {

	public final SugaredExpression expr;

	public SugaredOldExpression(SugaredExpression expr, int sourceStart, int sourceEnd) {
		super(expr.type, sourceStart, sourceEnd);
		this.expr = expr;
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "\\old("+this.expr.toString()+")"; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
