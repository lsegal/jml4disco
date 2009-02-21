package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.impl.BooleanConstant;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.lookup.JmlSpecialTypeBinding;

/** Informal expressions are used in predicates but also in
 * store ref lists.
 */
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
		this.constant = Constant.NotAConstant;
		return JmlSpecialTypeBinding.INFORMAL_COMMENT_UNFIXED_TYPE;
		// TypeBinding.BOOLEAN;
	}

}
