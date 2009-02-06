package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public class SugaredArrayReference extends SugaredAssignable {

	public final SugaredExpression receiver;
	public final SugaredExpression position;

	public SugaredArrayReference(SugaredExpression receiver, SugaredExpression position, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.receiver = receiver;
		this.position = position;
	}

	public String getName() {
		return this.receiver.toString();
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "{"+this.receiver+"[|"+this.position+"|]}";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
	}

}
