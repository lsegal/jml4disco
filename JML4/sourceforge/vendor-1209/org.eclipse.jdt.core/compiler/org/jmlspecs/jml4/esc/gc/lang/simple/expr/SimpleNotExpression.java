package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;

public class SimpleNotExpression extends SimpleUnaryExpression {
	public SimpleNotExpression(SimpleExpression expr, int sourceStart, int sourceEnd) {
		super(expr, sourceStart, sourceEnd);
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[Not "+this.expr+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
