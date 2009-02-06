package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgVariable extends CfgAssignable {

	public final String name;
	public final int    pos;
	public final  boolean isStaticField;

	public CfgVariable(String name, int pos, TypeBinding type, int incarnation, int sourceStart, int sourceEnd, boolean isStaticField) {
		super(incarnation, type, sourceStart, sourceEnd);
		this.name = name;
		this.pos  = pos;
		this.isStaticField = isStaticField;
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgAssignable withIncarnation(int newIncarnation) {
		return new CfgVariable(this.name, this.pos, this.type, newIncarnation, sourceStart, sourceEnd, this.isStaticField);
	}

	public String toString() {
		return this.name + "@" + this.pos + "$" + incarnation(); //$NON-NLS-1$ //$NON-NLS-2$
	}

	public String getName() {
		return this.name;
	}

	public boolean isVariable() {
		return true;
	}

}
