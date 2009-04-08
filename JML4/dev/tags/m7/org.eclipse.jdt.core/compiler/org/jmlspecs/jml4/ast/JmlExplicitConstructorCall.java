package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.ExplicitConstructorCall;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.jmlspecs.jml4.nonnull.Nullity;


public class JmlExplicitConstructorCall extends ExplicitConstructorCall {

	public JmlExplicitConstructorCall(int accessMode) {
		super(accessMode);
	}

	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		if (currentScope.compilerOptions().useNonNullTypeSystem()) {
			checkNullityOfParameters(currentScope, flowContext, flowInfo);
		}
		return super.analyseCode(currentScope, flowContext, flowInfo);		
	}
	private void checkNullityOfParameters(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		Expression[] actualParams = this.arguments;
		if (actualParams == null || this.binding == null) {
			return ;
		}
		AbstractMethodDeclaration sourceMethod = this.binding.sourceMethod();
		if (sourceMethod == null)
			return ;
		
		Argument[] formalParams = sourceMethod.arguments;
		for (int x = 0; x < actualParams.length; x++) {
			if (!Nullity.isAssignable(formalParams[x].type, actualParams[x], currentScope, flowContext, flowInfo)) {
				String formalName = new String(formalParams[x].name);
				currentScope.problemReporter().attemptToSendNullValue(this, x+1, formalName);
			}
		}		
	}
}

