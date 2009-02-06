package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public final class CfgBooleanConstant extends CfgExpression {

	public static final CfgBooleanConstant TRUE  = new CfgBooleanConstant(true,  0, 0);
	public static final CfgBooleanConstant FALSE = new CfgBooleanConstant(false, 0, 0);

	public  final boolean value;
	private final String name;
	
	public CfgBooleanConstant(boolean value, int sourceStart, int sourceEnd) {
		super(TypeBinding.BOOLEAN, sourceStart, sourceEnd);
		this.value = value;
		this.name = value ? "True" : "False";  //$NON-NLS-1$//$NON-NLS-2$
	}

	public String toString() {
		return this.name;
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}
}
