package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public class SugaredAssignment extends SugaredExpression {
	public final SugaredAssignable lhs;
	public final SugaredExpression expr;

	public SugaredAssignment(SugaredAssignable lhs, SugaredExpression expr, int sourceStart, int sourceEnd) {
		super(lhs.type, sourceStart, sourceEnd);
		this.lhs = lhs;
		this.expr = expr;
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}
	public SugaredExpression  accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}
	public String toString() {
		return "["+this.lhs+" := "+this.expr+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
