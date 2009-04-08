package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public abstract class SimpleAssignable extends SimpleExpression {

	public SimpleAssignable(TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
	}

	public abstract String getName();

	//* equality is only from the point of view of the incarnation map
	public abstract boolean equals(Object that);
	//* hasCode equality is only from the point of view of the incarnation map
	public abstract int hashCode();

	public boolean isField() {
		return false;
	}

	public boolean isVariable() {
		return false;
	}

}
