package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public class SugaredIntegerConstant extends SugaredExpression {

	public static final SugaredIntegerConstant      ZERO = new SugaredIntegerConstant( 0, 0, 0);
	public static final SugaredIntegerConstant       ONE = new SugaredIntegerConstant( 1, 0, 0);
	public static final SugaredIntegerConstant MINUS_ONE = new SugaredIntegerConstant(-1, 0, 0);
	
	public final int value;

	public SugaredIntegerConstant(int value, int sourceStart, int sourceEnd) {
		super(TypeBinding.INT, sourceStart, sourceEnd);
		this.value = value;
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression  accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[" + this.value + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
