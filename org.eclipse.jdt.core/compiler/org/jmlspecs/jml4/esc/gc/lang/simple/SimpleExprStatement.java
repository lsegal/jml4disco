package org.jmlspecs.jml4.esc.gc.lang.simple;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleMessageSend;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimplePostfixExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleVariable;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleExprStatement extends SimpleStatement {

	public final SimpleExpression expr;

	public SimpleExprStatement(SimpleExpression expr) {
		super(expr.sourceStart);
		Utils.assertTrue(expr instanceof SimpleVariable 
				|| expr instanceof SimpleMessageSend
				|| expr instanceof SimpleAssignment
				|| expr instanceof SimplePostfixExpression, 
				"expr '"+expr.toString()+"' expected to be an assignment or variable, but is a "+expr.getClass().getName()); //$NON-NLS-1$ //$NON-NLS-2$
		this.expr = expr;
	}

	public CfgStatement accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public String toString() {
		return this.expr.toString();
	}
}
