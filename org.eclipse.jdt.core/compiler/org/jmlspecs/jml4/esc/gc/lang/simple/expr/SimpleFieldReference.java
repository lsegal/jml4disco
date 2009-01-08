package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;

public class SimpleFieldReference extends SimpleAssignable {

	public final SimpleExpression receiver;
	public final String field;
	public final String declaringClass;

	public SimpleFieldReference(SimpleExpression receiver, String field, String declaringClass, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.receiver = receiver;
		this.field = field;
		this.declaringClass = declaringClass;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "["+this.receiver+"."+this.field+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public int hashCode() {
		int prime = 31;
		int result = 1;
		result = result * prime + this.field.hashCode();
		result = result * prime + this.declaringClass.hashCode();
		return result;
	}

	public boolean equals(Object that) {
		if (this == that)
			return true;
		if (that == null || this.getClass() != that.getClass())
			return false;
		return (this.field.equals(((SimpleFieldReference) that).field)
			&&  this.declaringClass.equals(((SimpleFieldReference) that).declaringClass));
	}

	public String getName() {
		return this.field;
	}

	public boolean isField() {
		return true;
	}

}
