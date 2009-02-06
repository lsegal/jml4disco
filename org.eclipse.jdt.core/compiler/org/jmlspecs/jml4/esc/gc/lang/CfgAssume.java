package org.jmlspecs.jml4.esc.gc.lang;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgAssume extends CfgStatement {
	public final CfgExpression pred;

	public CfgAssume(CfgExpression pred, int sourceStart) {
		super(sourceStart);
		Utils.assertTrue(pred.type == TypeBinding.BOOLEAN, "expr is not a boolean but a '"+pred.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		this.pred = pred;
	}

	public String toString() {
		return "[CfgAssume: " + this.pred + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public VC accept(WlpVisitor visitor, VC N) {
		VC result = visitor.visit(this, N);
		Utils.assertTrue(result.type == TypeBinding.BOOLEAN, "result is not a boolean but a '"+result.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		return result;
	}

}
