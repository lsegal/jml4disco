package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.AllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlAllocationExpression extends AllocationExpression {

	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		if (currentScope.compilerOptions().useNonNullTypeSystem()) {
			checkNullityOfParameters(currentScope, flowContext, flowInfo);
		}
		return super.analyseCode(currentScope, flowContext, flowInfo);
	}

	private void checkNullityOfParameters(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		Expression[] actualParams = this.arguments;
		if (actualParams == null || this.binding == null) {
			// TODO: maybe we should probably complain if there is no binding?
			return;
		}
		AbstractMethodDeclaration sourceMethod = this.binding.sourceMethod();
		if (sourceMethod == null)
			return;
		
		Argument[] formalParams = sourceMethod.arguments;
		for (int i=0; i<actualParams.length; i++) {
			if (!Nullity.isAssignable(formalParams[i].type, actualParams[i], currentScope, flowContext, flowInfo)) {
				String formalName = new String(formalParams[i].name);
				currentScope.problemReporter().attemptToSendNullValue(this, i+1, formalName);
			}
		}
	}
	public int nullStatus(FlowInfo flowInfo) {
		if (this.isDeclaredNonNull())
			return FlowInfo.NON_NULL;
		else
		    return super.nullStatus(flowInfo);
	}
	public boolean isDeclaredNonNull() {
		if (this.binding != null) {
			TypeBinding returnTypeBinding = this.binding.returnType;
			if (Nullity.isPrimitiveType(returnTypeBinding)) {
				return true;
			}
			AbstractMethodDeclaration abstractDeclaration = this.binding.sourceMethod();
			if (abstractDeclaration instanceof MethodDeclaration) {
				TypeReference returnType = ((MethodDeclaration)abstractDeclaration).returnType;
				if (returnType instanceof JmlTypeReference) {
					Nullity nullity = ((JmlTypeReference)returnType).getNullity();
					return nullity.isNon_null();
				}
			}
		}
		return false;
	}
	public boolean isDeclaredMonoNonNull() {
		if (this.binding != null) {
			TypeBinding returnTypeBinding = this.binding.returnType;
			if (Nullity.isPrimitiveType(returnTypeBinding)) {
				return true;
			}
			AbstractMethodDeclaration abstractDeclaration = this.binding.sourceMethod();
			if (abstractDeclaration instanceof MethodDeclaration) {
				TypeReference returnType = ((MethodDeclaration)abstractDeclaration).returnType;
				if (returnType instanceof JmlTypeReference) {
					Nullity nullity = ((JmlTypeReference)returnType).getNullity();
					return nullity.isMono_non_null();
				}
			}
		}
		return false;
	}
}
