package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredBinaryExpression extends SugaredExpression {

	public final SugaredExpression left;
	public final SugaredExpression right;
	public final SugaredOperator operator;

	public SugaredBinaryExpression(SugaredOperator operator, SugaredExpression left, SugaredExpression right, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		Utils.assertNotNull(left, "left is null"); //$NON-NLS-1$
		Utils.assertNotNull(right, "right is null"); //$NON-NLS-1$
		Utils.assertTrue(operator != SugaredOperator.IMPLIES || type == TypeBinding.BOOLEAN, "implies not a boolean but a '"+type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		this.left = left;
		this.right = right;
		this.operator = operator;
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "(" + this.left +  //$NON-NLS-1$
		       " " + this.operator + //$NON-NLS-1$
		       " " + this.right + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}