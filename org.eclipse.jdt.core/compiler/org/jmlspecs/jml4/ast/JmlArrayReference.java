package org.jmlspecs.jml4.ast;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.ArrayReference;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlArrayReference extends ArrayReference {

	public JmlArrayReference(Expression rec, Expression pos) {
		super(rec, pos);
	}

	public int nullStatus(FlowInfo flowInfo) {
		if (this.isDeclaredNonNull())
			return FlowInfo.NON_NULL;
		else
			return super.nullStatus(flowInfo);
	}

	private static class IntBinding {
		final int levels;
		final Binding binding;
		IntBinding(int l, Binding b) {this.levels = l; this.binding = b; }
	}

	// FIXME: eventually do this the OO way!
	private IntBinding getBindingAndLevels(Expression rcvr) {
		int levels = 0;
		Binding binding;
		while (true) {
			if (rcvr instanceof JmlSingleNameReference) {
				binding = ((JmlSingleNameReference)rcvr).binding;
				break;
			} else if (rcvr instanceof JmlQualifiedNameReference) {
				binding = ((JmlQualifiedNameReference)rcvr).binding;
				break;
			} else if (rcvr instanceof JmlFieldReference) {
				binding = ((JmlFieldReference)rcvr).binding;
				break;
			} else if (rcvr instanceof JmlArrayReference) {
				rcvr = ((JmlArrayReference)rcvr).receiver;
				levels++;
			} else if (rcvr instanceof JmlMessageSend) {
				binding = ((JmlMessageSend)rcvr).binding;
				break;
			} else if (rcvr instanceof JmlCastExpressionWithoutType) {
				rcvr = ((JmlCastExpressionWithoutType)rcvr).expression;
				// FIXME: (maybe) reset level?
			} else {
				String s = rcvr.getClass().getName();
				Assert.isTrue(false, "unexpected receiver type: " + s); //$NON-NLS-1$
			}
		}
		return new IntBinding(levels, binding);
	}
	private /*@nullable*/ Nullity[] getElementNullities(Binding binding) {
		Nullity[] elemNullities;
		if (binding instanceof FieldBinding) {
			FieldDeclaration fieldDecl = ((FieldBinding)binding).fieldDeclaration;
			if (fieldDecl == null) return null;
			if (fieldDecl.type instanceof JmlArrayQualifiedTypeReference)
				elemNullities = ((JmlArrayQualifiedTypeReference)(fieldDecl.type)).elemNullities;
			else if (fieldDecl.type instanceof JmlArrayTypeReference)
				elemNullities = ((JmlArrayTypeReference)(fieldDecl.type)).elemNullities;
			else {
				// String s = fieldDecl.type.getClass().getName();
				// Assert.isTrue(false, s+" is not handled"); //$NON-NLS-1$
				elemNullities = null;
			}
		} else if (binding instanceof LocalVariableBinding) {
			LocalDeclaration localDecl = ((LocalVariableBinding)binding).declaration;
			if (localDecl == null) return null;
			if (localDecl.type instanceof JmlParameterizedSingleTypeReference) {
				// JmlParameterizedSingleTypeReference type = ((JmlParameterizedSingleTypeReference)(localDecl.type));
				// ArrayBinding arrayBinding = (ArrayBinding)type.resolvedType;
				// FIXME: do something meaningful here instead
				return null;
			} else if (localDecl.type instanceof JmlSingleTypeReference) {
				elemNullities = null; //((JmlSingleTypeReference)(localDecl.type));
			} else if (localDecl.type instanceof JmlArrayTypeReference) {
				elemNullities = ((JmlArrayTypeReference)(localDecl.type)).elemNullities;
			} else if (localDecl.type instanceof JmlArrayQualifiedTypeReference) {
				elemNullities = ((JmlArrayQualifiedTypeReference)(localDecl.type)).elemNullities;
			} else {
				// String s = localDecl.type.getClass().getName();
				// Assert.isTrue(false, s+" is not handled"); //$NON-NLS-1$
				elemNullities = null;
			}
		} else if (binding instanceof MethodBinding) {
			AbstractMethodDeclaration methodDecl = ((MethodBinding)binding).methodDeclaration;
			if (methodDecl == null) return null;
			Assert.isTrue(methodDecl instanceof MethodDeclaration);
			elemNullities = ((JmlArrayTypeReference)(((MethodDeclaration)methodDecl).returnType)).elemNullities;
		} else {
			Assert.isTrue(false);
			elemNullities = null;
		}
		return elemNullities;
	}
	public boolean isDeclaredNonNull() {
		IntBinding intBinding = getBindingAndLevels(this.receiver);
		Binding binding = intBinding.binding;
		int levels = intBinding.levels;
		Nullity[] elemNullities = getElementNullities(binding);
		//TODO: is this if meaningful?
		//      why isn't there just the else clause?
		// how does elemNullities ever get to be null?
		if (elemNullities == null)
			return true;
//			return this.receiver.isDeclaredNonNull();
		else
			return elemNullities[levels].isNon_null();
	}

	public boolean isDeclaredMonoNonNull() {
		IntBinding intBinding = getBindingAndLevels(this.receiver);
		Binding binding = intBinding.binding;
		int levels = intBinding.levels;
		Nullity[] elemNullities = getElementNullities(binding);
		//TODO: is this if meaningful?
		//      why isn't there just the else clause?
		// how does elemNullities ever get to be null?
		if (elemNullities == null)
			return true;
//			return this.receiver.isDeclaredNonNull();
		else
			return elemNullities[levels].isMono_non_null();
	}
	protected void generateTestForNullity(BlockScope currentScope, CodeStream codeStream) {
		if (!currentScope.compilerOptions().jmlRacEnabled)
			   return;
		if (! Nullity.isPrimitiveType(this.resolvedType)  
		 && (this.isDeclaredNonNull() || this.isDeclaredMonoNonNull())) {
		   JmlCastExpression.generateTestForNullity(currentScope, codeStream, this.receiver.toString());
		}
	}
}
