package org.jmlspecs.jml4.esc.gc;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleThisReference;

public class SimpleSuperReference extends SimpleThisReference {

	public SimpleSuperReference(TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[super]"; //$NON-NLS-1$
	}

}
