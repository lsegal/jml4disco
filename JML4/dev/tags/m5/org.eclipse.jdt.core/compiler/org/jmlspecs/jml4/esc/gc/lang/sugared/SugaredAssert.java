package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredAssert extends SugaredStatement  {

	public static final SugaredStatement SKIP = new SugaredAssert(new SugaredBooleanConstant(true, 0, 0), KindOfAssertion.ASSERT, 0);
	
	public final SugaredExpression pred;
	public final KindOfAssertion kind;

	public SugaredAssert(SugaredExpression pred, KindOfAssertion kind, int sourceStart) {
		super(sourceStart);
		Utils.assertTrue(pred.type == TypeBinding.BOOLEAN, "pred is not a boolean but a '"+pred.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		Utils.assertTrue(kind==KindOfAssertion.ASSERT 
				|| sourceStart != 0, "sourceStart is 0 for a real assert('"+kind+"')"); //$NON-NLS-1$ //$NON-NLS-2$
		this.pred = pred;
		this.kind = kind;
	}

	public SimpleStatement accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredStatement accept(SimplifyingVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredStatement accept(DesugarLoopVisitor visitor, SugaredStatement rest) {
		return visitor.visit(this, rest);
	}

	public String toString() {
		return "[SugaredAssert(" + this.kind + "): "+this.pred.toString()+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
