package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgConditionalExpression extends CfgExpression {

	public final CfgExpression condition;
	public final CfgExpression valueIfTrue;
	public final CfgExpression valueIfFalse;

	public CfgConditionalExpression(CfgExpression condition,
			CfgExpression valueIfTrue, CfgExpression valueIfFalse, 
			TypeBinding type,
			int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		Utils.assertNotNull(condition);
		Utils.assertNotNull(valueIfTrue);
		Utils.assertNotNull(valueIfFalse);
		this.condition = condition;
		this.valueIfTrue = valueIfTrue;
		this.valueIfFalse = valueIfFalse;
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "( " + this.condition + " ? " + this.valueIfTrue + ":" + this.valueIfFalse + ")";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

}
