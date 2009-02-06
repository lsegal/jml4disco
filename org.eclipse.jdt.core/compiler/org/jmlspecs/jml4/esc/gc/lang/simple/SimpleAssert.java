package org.jmlspecs.jml4.esc.gc.lang.simple;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleAssert extends SimpleStatement {

	public static final SimpleStatement SKIP = new SimpleAssert(new SimpleBooleanConstant(true, 0, 0), KindOfAssertion.ASSERT, 0);
	public final SimpleExpression pred;
	public final KindOfAssertion kind;

	public SimpleAssert(SimpleExpression pred, KindOfAssertion kind, int sourceStart) {
		super(sourceStart);
		Utils.assertTrue(pred.type == TypeBinding.BOOLEAN, "pred is not a boolean but a '"+pred.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		this.pred = pred;
		this.kind = kind;
	}

	public String toString() {
		return "[SimpleAssert(" + this.kind + "): " + this.pred + "]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public CfgStatement accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}
}
