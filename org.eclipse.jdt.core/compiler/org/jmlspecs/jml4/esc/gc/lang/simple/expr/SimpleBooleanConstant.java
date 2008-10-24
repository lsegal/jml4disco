package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;

public final class SimpleBooleanConstant extends SimpleExpression {

	public final boolean value;
	private final String name;

	public SimpleBooleanConstant(boolean value, int sourceStart, int sourceEnd) {
		super(TypeBinding.BOOLEAN, sourceStart, sourceEnd);
		this.value = value;
		this.name = value ? "True" : "False";  //$NON-NLS-1$//$NON-NLS-2$
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[" + this.name + "]"; //$NON-NLS-1$//$NON-NLS-2$
	}

}
