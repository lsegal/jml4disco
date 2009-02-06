package org.jmlspecs.jml4.esc.gc.lang.simple;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleAssume extends SimpleStatement {
	public final SimpleExpression pred;

	public SimpleAssume(SimpleExpression pred, int sourceStart) {
		super(sourceStart);
		Utils.assertTrue(pred.type == TypeBinding.BOOLEAN, "pred is not a boolean but a '"+pred.type+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		this.pred = pred;
	}

	public String toString() {
		return "[SimpleAssume: " + this.pred + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public CfgStatement accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

}
