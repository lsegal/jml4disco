package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public class SugaredNotExpression extends SugaredUnaryExpression {
	public SugaredNotExpression(SugaredExpression expr, int sourceStart, int sourceEnd) {
		super(expr, sourceStart, sourceEnd);
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression  accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[Not "+this.expr+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
