package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ConditionalExpression;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;

public class JmlConditionalExpression extends ConditionalExpression {

	private int nullStatus = 0;
	private boolean nullStatusSet = false;

	public JmlConditionalExpression(Expression condition,
			Expression valueIfTrue, Expression valueIfFalse) {
		super(condition, valueIfTrue, valueIfFalse);
	}
	public int nullStatus(FlowInfo flowInfo) {
		return (this.nullStatusSet 
				? this.nullStatus
				: super.nullStatus(flowInfo));
	}
	protected void setNullStatus(int nullStatusWhenTrue, int nullStatusWhenFalse) {
		this.nullStatusSet = true;
		this.nullStatus = (nullStatusWhenTrue == nullStatusWhenFalse
							? nullStatusWhenTrue
							: FlowInfo.UNKNOWN);
	}
}
