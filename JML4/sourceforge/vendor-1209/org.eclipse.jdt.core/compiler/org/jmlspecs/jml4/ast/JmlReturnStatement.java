package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.ReturnStatement;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.impl.ReferenceContext;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;
import org.jmlspecs.jml4.compiler.JmlConstants;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlReturnStatement extends ReturnStatement {

	public JmlReturnStatement(/*@nullable*/ Expression expression, int sourceStart, int sourceEnd) {
		super(expression, sourceStart, sourceEnd);
	}
	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		FlowInfo fromSuper = super.analyseCode(currentScope, flowContext, flowInfo);
		if (this.expression != null) {
			checkNullity(currentScope, flowContext, flowInfo);
		}
        return fromSuper;
	}
	private boolean isDeclaredToReturnNonNull(BlockScope currentScope) {
		MethodScope methodScope = currentScope.methodScope();
		if (methodScope.referenceContext instanceof MethodDeclaration) {
			TypeReference returnType = ((MethodDeclaration)methodScope.referenceContext).returnType;
			if (returnType instanceof JmlTypeReference) {
				Nullity nullity = ((JmlTypeReference)returnType).getNullity();
				return nullity.isNon_null();
			}
		}
		return false;
	}
	//@ requires this.expression != null;
	private void checkNullity(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		MethodScope methodScope = currentScope.methodScope();
		if (methodScope.referenceContext instanceof MethodDeclaration) {
			TypeReference returnType = ((MethodDeclaration)methodScope.referenceContext).returnType;
			if (!Nullity.isAssignable(returnType, this.expression, methodScope, flowContext, flowInfo)) {
				currentScope.problemReporter().attemptToReturnNullValue(this);
			}
		}
	}

//	// FIXME: Perry can't recall what this is for :) ... so remove it eventually.
//	protected void handleDefinitelyAssignedVariables(BlockScope currentScope,
//			CodeStream codeStream) {
//		if (this.initStateIndex != -1) {
//			codeStream.removeNotDefinitelyAssignedVariables(currentScope, this.initStateIndex);
//			codeStream.addDefinitelyAssignedVariables(currentScope, this.initStateIndex);
//		}
//	}
	
	protected void generateOfPostCondition(BlockScope currentScope, CodeStream codeStream) {
		if (!currentScope.compilerOptions().jmlRacEnabled ||
				JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_GENERATION)
			return;
		generateCheckForNonNull(currentScope, codeStream);
		
		ReferenceContext referenceContext = currentScope.methodScope().referenceContext;
		final JmlMethodSpecification specification;
		final JmlLocalDeclaration result;
		if (referenceContext instanceof JmlMethodDeclaration) {
			JmlMethodDeclaration jmlMethodDeclaration = ((JmlMethodDeclaration)referenceContext);
			specification = jmlMethodDeclaration.specification;
			result = (jmlMethodDeclaration).resultValue;
		} else {
			//@ assert (referenceContext instanceof JmlConstructorDeclaration);
			JmlConstructorDeclaration jmlConstructorDeclaration = ((JmlConstructorDeclaration)referenceContext);
			specification = jmlConstructorDeclaration.specification;
			result = null;
		}
		if (specification != null) {
			if (result != null) {
				codeStream.store(result.binding, true);
			}
			//@ assert referenceContext instanceof AbstractMethodDeclaration;
			specification.generateCheckOfEnsures(currentScope, (AbstractMethodDeclaration)referenceContext, codeStream);
		}
	}
	protected void generateCheckForNonNull(BlockScope currentScope, CodeStream codeStream) {
		if (this.expression != null && 
			this.expression.resolvedType != null && 
			! Nullity.isPrimitiveType(this.expression.resolvedType)) {
			if (!currentScope.compilerOptions().jmlRacEnabled)
				return;

			if (isDeclaredToReturnNonNull(currentScope)) {
				JmlCastExpression.generateNullityTest(codeStream, "java/lang/NullPointerException", "RAC: return declared to be non-null"); //$NON-NLS-1$ //$NON-NLS-2$
			}
		}
	}
}
