package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.impl.BooleanConstant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlFreshExpression extends Expression {

	// TODO: check that the type of each arguments to fresh is non_null.

	private /*@non_null*/ Expression[] arguments;
	//@ invariant \nonnullelements(arguments);

	public JmlFreshExpression(Expression[] arguments) {
		this.arguments = arguments;
		// FIXME: temporary hack to ensure that code generation doesn't break ...
		this.constant = BooleanConstant.fromValue(true);
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		output.append("\\fresh("); //$NON-NLS-1$
		for (int i = 0; i < this.arguments.length; i++) {
			if (i > 0)
				output.append(", "); //$NON-NLS-1$
			this.arguments[i].printExpression(0, output);
		}
		return output.append(')');
	}

	public TypeBinding resolveType(BlockScope scope) {
		// TODO: resolve type of each arguments to fresh
		return TypeBinding.BOOLEAN;
	}
	
	// TODO:for RAC, fresh is considered non-executable.
}
