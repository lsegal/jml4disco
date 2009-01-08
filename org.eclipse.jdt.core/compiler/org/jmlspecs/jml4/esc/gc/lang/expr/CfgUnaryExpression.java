package org.jmlspecs.jml4.esc.gc.lang.expr;

public abstract class CfgUnaryExpression extends CfgExpression {

	public final CfgExpression expr;

	public CfgUnaryExpression(CfgExpression expr, int sourceStart, int sourceEnd) {
		super(expr.type, sourceStart, sourceEnd);
		this.expr = expr;
	}

}