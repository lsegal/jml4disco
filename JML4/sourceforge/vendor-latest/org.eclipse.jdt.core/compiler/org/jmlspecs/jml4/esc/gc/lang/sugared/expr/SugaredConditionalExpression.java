package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public class SugaredConditionalExpression extends SugaredExpression {

	public final SugaredExpression condition;
	public final SugaredExpression valueIfTrue;
	public final SugaredExpression valueIfFalse;

	public SugaredConditionalExpression(SugaredExpression condition,
			SugaredExpression valueIfTrue, SugaredExpression valueIfFalse,
			TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.condition = condition;
		this.valueIfTrue = valueIfTrue;
		this.valueIfFalse = valueIfFalse;
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression  accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[" + this.condition + " ? " + //$NON-NLS-1$//$NON-NLS-2$
				this.valueIfTrue + ":" + this.valueIfFalse + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
