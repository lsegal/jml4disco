package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlArrayIndexRangeExpression extends Expression {
	
	public /*@nullable*/ final Expression low;
	public /*@nullable*/ final Expression high;
	
	public JmlArrayIndexRangeExpression(/*@nullable*/ Expression lo, /*@nullable*/ Expression hi) {
		this.low = lo;
		this.high = hi;
	}

	public TypeBinding resolveType(BlockScope scope) {
		if (this.low != null) {
			if (this.low.resolveTypeExpecting(scope, TypeBinding.INT) == null)
				return null;
		}
		if (this.high != null) {
			if (this.high.resolveTypeExpecting(scope, TypeBinding.INT) == null)
				return null;
		}
		return TypeBinding.INT; // FIXME: ok to fake this? I.e. instead of using: JmlSpecialTypeBinding.MULTI_VALUE;
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		output.append(this.low);
		output.append(".."); //$NON-NLS-1$
		output.append(this.high);
		return output;
	}

}
