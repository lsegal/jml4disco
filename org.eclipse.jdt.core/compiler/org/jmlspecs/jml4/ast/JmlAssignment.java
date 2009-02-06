package org.jmlspecs.jml4.ast;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.ArrayBinding;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.jmlspecs.jml4.nonnull.Nullity;
import org.jmlspecs.jml4.util.Logger;

public class JmlAssignment extends Assignment {

	private static final boolean DEBUG = false;
	
	public JmlAssignment(Expression lhs, Expression expression, int sourceEnd) {
		super(lhs, expression, sourceEnd);
	}

	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		FlowInfo newFlowInfo = super.analyseCode(currentScope, flowContext, flowInfo); 
		if (currentScope.compilerOptions().useNonNullTypeSystem()) {
			checkNullity(currentScope, flowContext, newFlowInfo);
		}
		return newFlowInfo;
	}
	private void checkNullity(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		// TypeReference lhsType = null; 
		if (DEBUG)Logger.println("lhs  = '"+this.lhs.toString()+"' : "+this.lhs.getClass().toString()); //$NON-NLS-1$//$NON-NLS-2$
		if (DEBUG)Logger.println("expr = '"+this.expression.toString()+"' : "+this.expression.getClass().toString()); //$NON-NLS-1$//$NON-NLS-2$
		if (this.lhs.resolvedType instanceof ArrayBinding) {
			checkNullityOfArrayAssignment(this.expression, currentScope, flowContext, flowInfo);
		} else {
			checkNullityOfScalarAssignment(this.expression, currentScope, flowContext, flowInfo);
		}
	}

	private void checkNullityOfScalarAssignment(Expression rhs, BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		TypeReference lhsType;
		lhsType = getTypeReference(lhs, currentScope, flowContext, flowInfo);
		if (lhsType == null) {
			return;
		}
		if (DEBUG)Logger.println("lhs.isNonNull  = '"+lhs.nullStatus(flowInfo)+"' : "+lhs.getClass().toString()); //$NON-NLS-1$//$NON-NLS-2$
		if (DEBUG)Logger.println("expr.isNonNull = '"+rhs.nullStatus(flowInfo)+"' : "+rhs.getClass().toString()); //$NON-NLS-1$//$NON-NLS-2$
		if (DEBUG)Logger.println("FlowInfo.NULL     = '"+FlowInfo.NULL); //$NON-NLS-1$
		if (DEBUG)Logger.println("FlowInfo.NON_NULL = '"+FlowInfo.NON_NULL); //$NON-NLS-1$
		if (DEBUG)Logger.println("FlowInfo.UNKNOWN  = '"+FlowInfo.UNKNOWN); //$NON-NLS-1$

		if (!Nullity.isAssignable(lhsType, rhs, currentScope, flowContext, flowInfo)) {
			currentScope.problemReporter().attemptToAssignNullValue(this);
		}
	}

	private TypeReference getTypeReference(Expression exp, BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		TypeReference result = null;
		if (exp.localVariableBinding() != null) {
			result = exp.localVariableBinding().declaration.type;
		} else if (exp instanceof JmlSingleNameReference) {
			FieldBinding fieldBinding = ((JmlSingleNameReference) exp).fieldBinding(); 
			if (fieldBinding != null && fieldBinding.fieldDeclaration != null)
				result = fieldBinding.fieldDeclaration.type;
		} else if (exp instanceof JmlFieldReference) {
			FieldBinding fieldBinding = ((JmlFieldReference) exp).fieldBinding(); 
			if (fieldBinding != null && fieldBinding.fieldDeclaration != null)
				result = fieldBinding.fieldDeclaration.type;
		} else if (exp instanceof JmlArrayReference) {
			boolean leftIsNonNull = ((JmlArrayReference)exp).isDeclaredNonNull();
			if (leftIsNonNull && isNullable(this.expression, currentScope, flowContext, flowInfo)) {
			currentScope.problemReporter().attemptToAssignNullValue(this);
			}
			return null;
		} else if (exp instanceof JmlQualifiedNameReference) {
			JmlQualifiedNameReference qualifiedNameRef = (JmlQualifiedNameReference)exp;
			FieldBinding[] otherBindings = qualifiedNameRef.otherBindings;
 			Binding binding = otherBindings == null || otherBindings.length == 0  
 							? qualifiedNameRef.binding 
 			 				: otherBindings[otherBindings.length-1] ; // binding;
			
			if (binding instanceof FieldBinding) {
				FieldDeclaration fieldDecl = ((FieldBinding)binding).fieldDeclaration;
				if (fieldDecl != null)
					result = fieldDecl.type;
			} else if (binding instanceof LocalVariableBinding) {
				LocalDeclaration localDecl = ((LocalVariableBinding)binding).declaration;
				if (localDecl != null)
					result = localDecl.type;
			}
		} else {
			String type_name = exp.getClass().getName();
			Assert.isTrue(false && type_name != type_name, type_name+" not handled"); //$NON-NLS-1$
		}
		return result;
	}
	private void checkNullityOfArrayAssignment(Expression rhs, BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		Assert.isTrue(lhs.resolvedType instanceof ArrayBinding);
		// 1) check the nullity of the array references.
		checkNullityOfScalarAssignment(rhs, currentScope, flowContext, flowInfo);
		// FIXME: remove initial underscore from _test_00014_2d_fieldAssignment_initializers
		// FIXME: do more
		//        2) for each dimension, check that the nullities are equal 
		//           (since array assignment is invariant (for now))
	}

	private static boolean isNullable(Expression exp, BlockScope scope, FlowContext flowContext, FlowInfo flowInfo) {
		if (exp.isDeclaredNonNull()) {
			return false;
		} 
		if (exp.localVariableBinding() == null) {
			return true;
		}
		Nullity.preparePossibleUnknowns(exp, scope, flowContext, flowInfo);
		return ! (exp.nullStatus(flowInfo) == FlowInfo.NON_NULL);
	}
	public int nullStatus(FlowInfo flowInfo) {
		if (this.lhs instanceof FieldReference) {
           if (this.lhs.isDeclaredNonNull())
        	   return FlowInfo.NON_NULL;
           else
        	   return FlowInfo.UNKNOWN;
		} else
		   return super.nullStatus(flowInfo);
	}

	public boolean isDeclaredNonNull() {
		return this.lhs.isDeclaredNonNull();
	}
	public boolean isDeclaredMonoNonNull() {
		return this.lhs.isDeclaredMonoNonNull();
	}
	
	public void traverse(ASTVisitor visitor, BlockScope scope) {
		if (visitor.visit(this, scope)) {
			super.traverse(visitor, scope);
		}
		visitor.endVisit(this, scope);
	}
}
