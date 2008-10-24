package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public abstract class CfgAssignable extends CfgExpression {

	private int incarnation;

	public CfgAssignable(int incarnation, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.incarnation = incarnation;
	}

	public abstract String getName();
	public abstract CfgAssignable withIncarnation(int newIncarnation);
	
	public boolean isField() {
		return false;
	}
	public boolean isVariable() {
		return false;
	}

	public void setIncarnation(int newIncarnation) {
		this.incarnation = newIncarnation;
	}

	public int incarnation() {
		return this.incarnation;
	}

}
