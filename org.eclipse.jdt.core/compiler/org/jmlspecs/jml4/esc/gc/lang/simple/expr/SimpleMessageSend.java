package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleVarDecl;

public class SimpleMessageSend extends SimpleExpression {

	public final SimpleExpression receiver;
	public final String selector; 
	public final SimpleVarDecl[] formalParams; 
	public final SimpleExpression[] actualParams; 
	public final SimpleExpression pre; 
	public final SimpleExpression post;
	public final int countForLabels;
	
	public SimpleMessageSend(int countForLabels, SimpleExpression receiver, String selector, 
			SimpleVarDecl[] formalParams, SimpleExpression[] actualParams, TypeBinding type, 
			SimpleExpression pre, SimpleExpression post, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.receiver = receiver;
		this.selector = selector;
		this.formalParams = formalParams;
		this.actualParams = actualParams;
		this.pre = pre;
		this.post = post;
		this.countForLabels = countForLabels;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}


	public String toString() {
		StringBuffer params = new StringBuffer();
		for (int i = 0; i < this.actualParams.length; i++) {
			if (i > 0) 
				params.append(", "); //$NON-NLS-1$
			params.append(this.actualParams[i].toString());
		}
		return "["+type.toString()+":"+selector+" ("+params.toString()+")]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

}
