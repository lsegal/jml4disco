package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public final class SugaredBooleanConstant extends SugaredExpression {

	public static final SugaredBooleanConstant TRUE = new SugaredBooleanConstant(true, 0, 0);
	private final String name;
	public  final boolean value;

	public SugaredBooleanConstant(boolean value, int sourceStart, int sourceEnd) {
		super(TypeBinding.BOOLEAN, sourceStart, sourceEnd);
		this.value = value;
		this.name = value ? "True" : "False";  //$NON-NLS-1$//$NON-NLS-2$
	}

	public String toString() {
		return "[" + this.name + "]";  //$NON-NLS-1$//$NON-NLS-2$
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression  accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

}
