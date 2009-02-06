package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleVariable extends SimpleAssignable {

	public final String  name;
	public final int     pos;
	public final boolean isStaticField;

	public SimpleVariable(String name, int pos, TypeBinding type, int sourceStart, int sourceEnd, boolean isStaticField) {
		super(type, sourceStart, sourceEnd);
		Utils.assertNotNull(type , "type of "+name+" is null");  //$NON-NLS-1$//$NON-NLS-2$
		Utils.assertTrue(type != TypeBinding.VOID, "type of "+name+" is void"); //$NON-NLS-1$ //$NON-NLS-2$
		this.name = name;
		this.pos = pos;
		this.isStaticField = isStaticField;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "[" + this.name + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public int hashCode() {
		int prime = 31;
		int result = 1;
		result = result * prime + name.hashCode();
		result = result * prime + this.pos;
		return result;
	}

	public boolean equals(Object that) {
		if (this == that)
			return true;
		if (that == null || this.getClass() != that.getClass())
			return false;
		return (name.equals(((SimpleVariable) that).name)
			&&  this.pos == ((SimpleVariable) that).pos);
	}

	public String getName() {
		return this.name;
	}

	public boolean isVariable() {
		return true;
	}

}