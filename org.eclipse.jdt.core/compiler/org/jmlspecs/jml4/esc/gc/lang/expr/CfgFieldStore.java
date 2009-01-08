package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

import escjava.vcGeneration.TBoolAnd;

public class CfgFieldStore extends CfgExpression {

	public final CfgFieldReference field;
	public final int oldIncarnation;
	public final int newIncarnation;
	public final CfgExpression value;

	public CfgFieldStore(CfgFieldReference field, int oldIncarnation, int newIncarnation, CfgExpression value) {
		super(TypeBinding.BOOLEAN, field.sourceStart, field.sourceEnd);
		this.field = field;
		this.oldIncarnation = oldIncarnation;
		this.newIncarnation = newIncarnation;
		this.value = value;
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "["+this.field.field+"("+newIncarnation+") := " +   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		"(["+this.field.receiver+"."+this.field.field+"("+oldIncarnation+")] ->"+  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		this.value+")]"; //$NON-NLS-1$
	}

}
