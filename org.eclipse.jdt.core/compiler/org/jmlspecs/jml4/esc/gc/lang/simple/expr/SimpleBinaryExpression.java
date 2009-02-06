package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleBinaryExpression extends SimpleExpression {

	public final SimpleExpression left;
	public final SimpleExpression right;
	public final SimpleOperator   operator;
	
	public SimpleBinaryExpression(SimpleOperator operator, SimpleExpression left, SimpleExpression right, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		Utils.assertTrue(operator != SimpleOperator.IMPLIES || type == TypeBinding.BOOLEAN, "implies not a boolean but a '"+type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
        this.operator = operator;
		this.left = left;
		this.right = right;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}
	
	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "(" + this.left +  //$NON-NLS-1$
		       " " + this.operator + //$NON-NLS-1$
		       " " + this.right + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
