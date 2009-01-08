package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgNotExpression extends CfgUnaryExpression {
	public CfgNotExpression(CfgExpression expr, int sourceStart, int sourceEnd) {
		super(expr, sourceStart, sourceEnd);
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "(! " +this.expr + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
