package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.UnaryExpression;

public class JmlUnaryExpression extends UnaryExpression {

	public JmlUnaryExpression(Expression expression, int operator) {
		super(expression, operator);
	}

}
