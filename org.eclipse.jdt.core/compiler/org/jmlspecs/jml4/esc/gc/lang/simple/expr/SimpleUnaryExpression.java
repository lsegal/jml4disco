package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

public abstract class SimpleUnaryExpression extends SimpleExpression {

	public final SimpleExpression expr;

	public SimpleUnaryExpression(SimpleExpression expr, int sourceStart, int sourceEnd) {
		super(expr.type, sourceStart, sourceEnd);
		this.expr = expr;
	}

}