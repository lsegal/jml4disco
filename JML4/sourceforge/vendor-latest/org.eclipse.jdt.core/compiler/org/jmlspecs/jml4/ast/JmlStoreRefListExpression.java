package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.lookup.JmlSpecialTypeBinding;

public class JmlStoreRefListExpression extends JmlMultiReferenceExpression {

	public final Expression[] exprList;
	
	
	public JmlStoreRefListExpression(Expression[] exprList) {
		this.exprList = exprList;
	}

	public TypeBinding resolveType(BlockScope scope) {
		for (int i = 0; i < this.exprList.length; i++) {
			Expression storeRef = this.exprList[i];
			TypeBinding type = storeRef.resolveType(scope);
			if (type == null)
				return null;
			if (storeRef instanceof Reference
				|| storeRef.isThis()
				|| type == JmlSpecialTypeBinding.INFORMAL_COMMENT_UNFIXED_TYPE
				// || type instanceof VariableBinding ? necessary?
				|| type == JmlSpecialTypeBinding.MULTI_REFERENCE_MAYBE_WITH_INFORMAL_COMMENTS)
			{
				// do nothing
			} else {
				String msg = "JML store reference expected"; //$NON-NLS-1$
				scope.problemReporter().jmlEsc2Error(msg, storeRef.sourceStart, storeRef.sourceEnd);
				return null;
			}
		}
		return JmlSpecialTypeBinding.MULTI_REFERENCE_MAYBE_WITH_INFORMAL_COMMENTS;
	}

	public FlowInfo analyseCode(BlockScope currentScope,
			FlowContext flowContext, FlowInfo flowInfo) {
		for (int i = 0; i < this.exprList.length; i++) {
			flowInfo = this.exprList[i].analyseCode(currentScope, flowContext, flowInfo);
		}
		return flowInfo;
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		for (int i = 0; i < this.exprList.length; i++) {
			if(i > 0)
				output.append(", "); //$NON-NLS-1$
			this.exprList[i].print(0, output);
		}
		return output;
	}

}
