package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredMessageSend extends SugaredExpression {

	public final SugaredExpression receiver;
	public final String selector; 
	public final SugaredVarDecl[] formalParams; 
	public final SugaredExpression[] actualParams; 
	public final SugaredExpression pre; 
	public final SugaredExpression post;
	public final int countForLabels;
	
	public SugaredMessageSend(int countForLabels, SugaredExpression receiver, String selector, SugaredVarDecl[] formalParams, SugaredExpression[] actualParams, TypeBinding type, SugaredExpression pre, SugaredExpression post, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		Utils.assertNotNull(receiver, "receiver is null"); //$NON-NLS-1$
		Utils.assertNotNull(selector, "selector is null"); //$NON-NLS-1$
		Utils.assertNotNull(formalParams, "formalParams is null"); //$NON-NLS-1$
		Utils.assertNotNull(actualParams, "actualParams is null"); //$NON-NLS-1$
		this.receiver = receiver;
		this.selector = selector;
		this.formalParams = formalParams;
		this.actualParams = actualParams;
		this.pre = pre;
		this.post = post;
		this.countForLabels = countForLabels;
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		StringBuffer params = new StringBuffer();
		for (int i = 0; i < this.actualParams.length; i++) {
			if (i > 0) 
				params.append(", "); //$NON-NLS-1$
			params.append(this.actualParams[i].toString());
		}
		return "["+type.toString()+":"+selector+" "+params.toString()+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

}
