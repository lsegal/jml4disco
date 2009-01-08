package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgBinaryExpression extends CfgExpression {

	public final CfgExpression left;
	public final CfgExpression right;
	public final CfgOperator   operator;
	
	public CfgBinaryExpression(CfgOperator operator, CfgExpression left, CfgExpression right, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		Utils.assertTrue(operator != CfgOperator.IMPLIES || type == TypeBinding.BOOLEAN, "implies not a boolean but a '"+type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		Utils.assertTrue(operator != CfgOperator.IMPLIES || left.type == TypeBinding.BOOLEAN, "left is not a boolean but a '"+left.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		Utils.assertTrue(operator != CfgOperator.IMPLIES || right.type == TypeBinding.BOOLEAN, "right is not a boolean but a '"+right.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		this.operator = operator;
		this.left = left;
		this.right = right;
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "(" + this.left +  //$NON-NLS-1$
		       " " + this.operator + //$NON-NLS-1$
		       " " + this.right + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}

}
