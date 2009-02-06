package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public abstract class SimpleExpression {
	
	public final TypeBinding type;
	public final int sourceStart;
	public final int sourceEnd;
	
	public SimpleExpression(TypeBinding type, int sourceStart, int sourceEnd) {
		Utils.assertTrue(sourceStart == 0 || sourceEnd == 0 || sourceStart <= sourceEnd, "source positions incorrect ("+sourceStart+">"+sourceEnd+")");   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		Utils.assertNotNull(type, "type is null"); //$NON-NLS-1$
		this.type = type;
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
	}
	public abstract CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap);
	public abstract SimpleExpression accept(SimpleExprVisitor visitor);
	public abstract String toString();
}
