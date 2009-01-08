package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;

public class SimplePostfixExpression extends SimpleExpression {

	public final SimpleAssignable lhs;
	public final SimpleOperator operator;

	public SimplePostfixExpression(SimpleAssignable lhs, SimpleOperator operator, int sourceStart, int sourceEnd) {
		super(lhs.type, sourceStart, sourceEnd);
		this.lhs = lhs;
		this.operator = operator;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		String op = this.operator.toString();
		return "(" + this.lhs + " " + op + op + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}
}
