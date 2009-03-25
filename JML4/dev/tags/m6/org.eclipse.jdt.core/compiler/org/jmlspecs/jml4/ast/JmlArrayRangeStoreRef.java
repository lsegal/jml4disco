package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.lookup.JmlSpecialTypeBinding;

public class JmlArrayRangeStoreRef extends JmlMultiReferenceExpression {
	private JmlArrayReference delegate;

	public JmlArrayRangeStoreRef(JmlArrayReference delegate) {
		this.delegate = delegate;
		this.sourceStart = delegate.sourceStart;
	}

	public TypeBinding resolveType(BlockScope scope) {
		TypeBinding type = this.delegate.resolveType(scope);
		if (type == null)
			return null;
		// FIXME: anything further to do with the array index range expression?
		return JmlSpecialTypeBinding.MULTI_REFERENCE_MAYBE_WITH_INFORMAL_COMMENTS;
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		return this.delegate.printExpression(indent, output);
	}
}
