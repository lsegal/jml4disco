package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.LabeledStatement;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlOldExpression extends JmlUnaryExpression {

	/* label is left as a char[] instead of converting it to a string because it is only used
	 * in comparisons to other char[]s in analyseCode().  otherwise, we'd store it as a String
	 * and use .toCharArray() (outside the loop) to get the char[] to compare with.
	 */
	private final /*@nullable*/ char[] label;
	
	public JmlOldExpression(Expression expression, int operator) {
		super(expression, operator);
		this.label = null;
	}
	
	public JmlOldExpression(Expression expression, int operator, char[] label) {
		super(expression, operator);
		this.label = label;
	}

	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {

		FlowContext current = flowContext;
		while (current != null) {
			char[] currentLabelName = current.labelName();
			if ((currentLabelName != null)
				&& CharOperation.equals(currentLabelName, this.label)) {
				((LabeledStatement)current.associatedNode).bits |= ASTNode.LabelUsed;
			}
			current = current.parent;
		}
		
		return flowInfo;
	}

	public TypeBinding resolveType(BlockScope scope) {
		super.resolveType(scope); // value from super ignored
		this.resolvedType = this.expression.resolvedType;
		return this.resolvedType;
	}

}
