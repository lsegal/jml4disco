package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgIntegerConstant extends CfgExpression {

	public static final CfgIntegerConstant ONE = new CfgIntegerConstant(1, 0, 0);

	public final int value;
	public CfgIntegerConstant(int value, int sourceStart, int sourceEnd) {
		super(TypeBinding.INT, sourceStart, sourceEnd);
		this.value = value;
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "" + this.value; //$NON-NLS-1$
	}

}
