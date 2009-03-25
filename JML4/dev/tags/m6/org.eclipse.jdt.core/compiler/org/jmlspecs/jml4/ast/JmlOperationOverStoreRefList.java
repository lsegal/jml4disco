package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlOperationOverStoreRefList extends JmlUnaryExpression {

	public JmlOperationOverStoreRefList(Expression argument, int operator) {
		super(argument, operator);
	}

	public TypeBinding resolveType(BlockScope scope) {
		this.constant = Constant.NotAConstant;
		return this.resolvedType = TypeBinding.BOOLEAN;
	}

	public void generateCode(BlockScope currentScope, CodeStream codeStream,
			boolean valueRequired) {
		return; // don't generate code.
	}

	public StringBuffer printExpressionNoParenthesis(int indent,
			StringBuffer output) {
		// We must print parentheses around arguments.
		output.append(operatorToString()).append('(');
		this.expression.printExpression(0, output);
		return output.append(')');
	}
}
