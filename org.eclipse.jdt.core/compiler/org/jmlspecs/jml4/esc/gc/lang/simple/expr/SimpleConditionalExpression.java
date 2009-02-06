package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;

public class SimpleConditionalExpression extends SimpleExpression {

	public final SimpleExpression condition;
	public final SimpleExpression valueIfTrue;
	public final SimpleExpression valueIfFalse;

	public SimpleConditionalExpression(SimpleExpression condition,
			SimpleExpression valueIfTrue, SimpleExpression valueIfFalse,
			TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.condition = condition;
		this.valueIfTrue = valueIfTrue;
		this.valueIfFalse = valueIfFalse;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[SimpleConditional: " + this.condition + " ? " + //$NON-NLS-1$//$NON-NLS-2$
				this.valueIfTrue + ":" + this.valueIfFalse + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
