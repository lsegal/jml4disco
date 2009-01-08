package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;

public class SugaredArrayAllocationExpression extends SugaredExpression {

	//* ids are for ensuring uniqueness, since the array being created will need a new temp name
	public final int[] ids;
	public final SugaredExpression[] dims;

	public SugaredArrayAllocationExpression(int[] ids, SugaredExpression[] dims, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.ids = ids;
		this.dims = dims;
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression accept(SugaredExpressionVisitor visitor) {
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
