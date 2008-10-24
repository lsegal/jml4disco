package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public class SugaredPostfixExpression extends SugaredExpression {

	public final SugaredAssignable lhs;
	public final SugaredOperator operator;

	public SugaredPostfixExpression(SugaredAssignable lhs, SugaredOperator operator, int sourceStart, int sourceEnd) {
		super(lhs.type, sourceStart, sourceEnd);
		this.lhs = lhs;
		this.operator = operator;
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression  accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		String op = this.operator.toString();
		return "(" + this.lhs + " " + op + op + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}
}
