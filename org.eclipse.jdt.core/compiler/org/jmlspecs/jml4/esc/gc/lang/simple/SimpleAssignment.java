package org.jmlspecs.jml4.esc.gc.lang.simple;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleAssignable;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public class SimpleAssignment extends SimpleExpression {
	public final SimpleAssignable lhs;
	public final SimpleExpression expr;

	public SimpleAssignment(SimpleAssignable lhs, SimpleExpression expr, int sourceStart, int sourceEnd) {
		super(lhs.type, sourceStart, sourceEnd);
		this.lhs = lhs;
		this.expr = expr;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[" + this.lhs + " := " + this.expr + "]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
