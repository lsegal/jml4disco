package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public abstract class CfgExpression {

	public final TypeBinding type;
	public final int sourceStart;
	public final int sourceEnd;
	
	public CfgExpression(TypeBinding type, int sourceStart, int sourceEnd) {
		this.type = type;
		Utils.assertNotNull(type, "type is null"); //$NON-NLS-1$
		Utils.assertTrue(sourceStart == 0 || sourceEnd == 0 || sourceStart <= sourceEnd, "source positions incorrect ("+sourceStart+">"+sourceEnd+")");   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
	}
	public abstract VC            accept(WlpVisitor visitor);
	public abstract CfgExpression accept(CfgExpressionVisitor visitor);
	public abstract String toString();

}
