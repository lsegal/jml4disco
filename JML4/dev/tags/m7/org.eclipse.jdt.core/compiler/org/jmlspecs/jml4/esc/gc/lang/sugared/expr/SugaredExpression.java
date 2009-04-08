package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public abstract class SugaredExpression {

	public static final SugaredExpression[] EMPTY = new SugaredExpression[0];
	public int sourceStart;
	public int sourceEnd;
	public final TypeBinding type;

	public SugaredExpression(TypeBinding type, int sourceStart, int sourceEnd) {
		Utils.assertTrue(sourceStart == 0 || sourceEnd == 0 || sourceStart <= sourceEnd, "source positions incorrect ("+sourceStart+">"+sourceEnd+")");   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		Utils.assertNotNull(type, "type is null"); //$NON-NLS-1$
		this.type = type;
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
	}
	public abstract SimpleExpression accept(DesugaringVisitor visitor);
	public abstract String toString();
	public abstract SugaredExpression accept(SugaredExpressionVisitor visitor);

	public void clearSourcePosition() {
		this.sourceStart = 0;
		this.sourceEnd = 0;
	}
	public boolean equals(Object obj) {
		if (obj == null || obj.getClass() != this.getClass())
			return false;
		return this.toString().equals(obj.toString());
	}
	public int hashCode() {
		return this.toString().hashCode();
	}
}
