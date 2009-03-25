package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredFieldReference extends SugaredAssignable {

	public final SugaredExpression receiver;
	public final String field;
	public final String declaringClass;

	public SugaredFieldReference(SugaredExpression receiver, String field, String declaringClass, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		Utils.assertNotNull(receiver, "receiver is null"); //$NON-NLS-1$
		this.receiver = receiver;
		this.field = field;
		this.declaringClass = declaringClass;
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "["+this.receiver+"."+this.field+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public String getName() {
		return this.field;
	}

	public boolean isVariable() {
		return true;
	}

}
