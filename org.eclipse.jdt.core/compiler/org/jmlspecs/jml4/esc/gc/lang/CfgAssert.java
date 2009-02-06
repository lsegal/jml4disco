package org.jmlspecs.jml4.esc.gc.lang;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgAssert extends CfgStatement {

   public static final CfgStatement SKIP = new CfgAssert(CfgBooleanConstant.TRUE, KindOfAssertion.ASSERT, 0);
   public final CfgExpression pred;
   public final KindOfAssertion kind;
   
   public CfgAssert(CfgExpression pred, KindOfAssertion kind, int sourceStart) {
	   super(sourceStart);
	   Utils.assertTrue(pred.type == TypeBinding.BOOLEAN, "pred is not a boolean but a '"+pred.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
	   Utils.assertTrue(!(kind == KindOfAssertion.PRE && sourceStart == 0), "pre@0"); //$NON-NLS-1$
	   this.pred = pred;
	   this.kind = kind;
   }

 	public String toString() {
		return "[CfgAssert(" + this.kind + "): " + this.pred + "]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public VC accept(WlpVisitor visitor, VC N) {
		return visitor.visit(this, N);
	}

}
