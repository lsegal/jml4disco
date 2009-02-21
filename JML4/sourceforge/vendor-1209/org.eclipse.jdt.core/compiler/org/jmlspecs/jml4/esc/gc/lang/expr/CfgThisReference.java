package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgThisReference extends CfgExpression {

	public CfgThisReference(TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[this]"; //$NON-NLS-1$
	}

}
