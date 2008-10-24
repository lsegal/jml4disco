package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;

public class SimpleIntegerConstant extends SimpleExpression {

	public final int value;

	public SimpleIntegerConstant(int value, int sourceStart, int sourceEnd) {
		super(TypeBinding.INT, sourceStart, sourceEnd);
		this.value = value;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[" + this.value + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
