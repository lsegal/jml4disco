package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgArrayReference extends CfgAssignable {

	public final CfgExpression receiver;
	public final CfgExpression position;

	public CfgArrayReference(CfgExpression receiver, CfgExpression position, int incarnation, TypeBinding type, int sourceStart, int sourceEnd) {
		super(incarnation, type, sourceStart, sourceEnd);
		this.receiver = receiver;
		this.position = position;
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "{"+this.receiver+"[|"+this.position+"|]}";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
	}

	public String getName() {
		return "<elems>"; //$NON-NLS-1$
	}

	public CfgAssignable withIncarnation(int newIncarnation) {
		return new CfgArrayReference(this.receiver, this.position, newIncarnation, this.type, sourceStart, sourceEnd);
	}

}
