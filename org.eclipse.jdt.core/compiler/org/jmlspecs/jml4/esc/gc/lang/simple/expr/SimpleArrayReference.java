package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;

public class SimpleArrayReference extends SimpleAssignable {

	public final SimpleExpression receiver;
	public final SimpleExpression position;

	public SimpleArrayReference(SimpleExpression receiver, SimpleExpression position, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.receiver = receiver;
		this.position = position;
	}

	public String getName() {
		return "<elems>"; //$NON-NLS-1$
	}

	//* equality is only from the point of view of the incarnation map
	//* so all array references are equal
	public boolean equals(Object that) {
		return (that instanceof SimpleArrayReference);
	}

	//* hasCode equality is only from the point of view of the incarnation map
	//* so all array references are equal
	public int hashCode() {
		int aNotTooBigPrime = 999999937;
		return aNotTooBigPrime;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "{"+this.receiver+"[|"+this.position+"|]}";  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
