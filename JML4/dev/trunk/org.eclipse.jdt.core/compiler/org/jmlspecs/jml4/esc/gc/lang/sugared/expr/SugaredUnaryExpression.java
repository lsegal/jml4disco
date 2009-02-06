package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

public abstract class SugaredUnaryExpression extends SugaredExpression {

	public final SugaredExpression expr;

	public SugaredUnaryExpression(SugaredExpression expr, int sourceStart, int sourceEnd) {
		super(expr.type, sourceStart, sourceEnd);
		this.expr = expr;
	}
}