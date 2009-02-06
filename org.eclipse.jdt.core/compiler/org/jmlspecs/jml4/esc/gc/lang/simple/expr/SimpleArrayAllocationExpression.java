package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;

public class SimpleArrayAllocationExpression extends SimpleExpression {

	public final int[] ids;
	public final SimpleExpression[] dims;

	public SimpleArrayAllocationExpression(int[] ids, SimpleExpression[] dims, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.ids = ids;
		this.dims = dims;
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		String sType = this.type.debugName();
		String sDims = getDimsAsString();
		return "new "+sType+sDims; //$NON-NLS-1$
	}

	private String getDimsAsString() {
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < this.dims.length; i++) {
			result.append("["+this.dims[i]+"]");  //$NON-NLS-1$//$NON-NLS-2$
		}
		return result.toString();
	}

}
