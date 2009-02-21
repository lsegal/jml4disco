package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.OperatorIds;
import org.eclipse.jdt.internal.compiler.ast.UnaryExpression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

/**
 * NOTE: operators taking a list of store ref, like \not_modified() are
 * modeled as unary operators -- taking a single argument consisting of the entire
 * list.
 */
public class JmlUnaryExpression extends UnaryExpression {

	public JmlUnaryExpression(Expression expression, int operator) {
		super(expression, operator);
	}

	public int operatorId() {
		return (bits & OperatorMASK) >> OperatorSHIFT;
	}

	public static JmlUnaryExpression factory(Expression expr, int op) {
		switch (op) {
		case OperatorIds.JML_NOT_ASSIGNED:
		case OperatorIds.JML_NOT_MODIFIED:
			return new JmlOperationOverStoreRefList(expr, op);
		default:
			return new JmlUnaryExpression(expr, op);
		}
	}
}
