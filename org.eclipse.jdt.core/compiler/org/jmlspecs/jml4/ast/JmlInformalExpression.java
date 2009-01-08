package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.impl.BooleanConstant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlInformalExpression extends Expression {

	private final String source;

	public JmlInformalExpression(char[] source, int startPos, int endPos) {
		this.source = new String(source);
		this.sourceStart = startPos;
		this.sourceEnd = endPos;
		// FIXME: should be either true or false or an exception at run-time.
		this.constant = BooleanConstant.fromValue(true);
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		return output.append(this.source);
	}

	public TypeBinding resolveType(BlockScope scope) {
		return TypeBinding.BOOLEAN;
	}

}
