package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public abstract class SugaredAssignable extends SugaredExpression {

	public SugaredAssignable(TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
	}

	public abstract String getName();

	public boolean isField() {
		return false;
	}

	public boolean isVariable() {
		return false;
	}

}
