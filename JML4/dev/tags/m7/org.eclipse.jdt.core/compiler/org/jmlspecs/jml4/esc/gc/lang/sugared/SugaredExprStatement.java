package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleExprStatement;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredAssignment;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredMessageSend;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredPostfixExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredVariable;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredExprStatement extends SugaredStatement {

	public final SugaredExpression expr;

	public SugaredExprStatement(SugaredExpression expr) {
		super(expr.sourceStart);
		Utils.assertTrue(expr instanceof SugaredVariable 
				|| expr instanceof SugaredAssignment
				|| expr instanceof SugaredMessageSend
				|| expr instanceof SugaredPostfixExpression, 
				"expr '"+expr.toString()+"'::"+expr.getClass().getName()+" expected to be an Assignment or Variable or Postfix"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		this.expr = expr;
	}

	public SimpleStatement accept(DesugaringVisitor visitor) {
		SimpleExpression simpExpr = this.expr.accept(visitor);
		return new SimpleExprStatement(simpExpr);
	}

	public SugaredStatement accept(SimplifyingVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredStatement accept(DesugarLoopVisitor visitor, SugaredStatement rest) {
		return visitor.visit(this, rest);
	}

	public String toString() {
		return this.expr.toString();
	}
}
