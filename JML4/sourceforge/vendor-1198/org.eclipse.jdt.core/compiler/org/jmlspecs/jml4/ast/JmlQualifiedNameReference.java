package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.AbstractVariableDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.QualifiedNameReference;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BinaryTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.jmlspecs.jml4.lookup.JmlBinaryLookup;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlQualifiedNameReference extends QualifiedNameReference {

	public JmlQualifiedNameReference(char[][] sources, long[] positions, int sourceStart, int sourceEnd) {
		super(sources, positions, sourceStart, sourceEnd);
	}

	public int nullStatus(FlowInfo flowInfo) {
		if (this.isDeclaredNonNull()) {
			return FlowInfo.NON_NULL;
		} else {
			return super.nullStatus(flowInfo);
		}
	}
	
	public boolean isDeclaredNonNull() {
		FieldBinding field = getFieldBinding();
		
		if (field == null)
			return false;
		if (Nullity.isPrimitiveType(field.type))
			return true;
		
		FieldDeclaration fieldDeclaration = getFieldDeclaration(field);
		if (fieldDeclaration != null) {
			if (field.isFinal() && fieldDeclaration.initialization != null )
				return fieldDeclaration.initialization.isDeclaredNonNull();
			if (fieldDeclaration.type instanceof JmlTypeReference) {
				Nullity nullity = ((JmlTypeReference)fieldDeclaration.type).getNullity();
				if (nullity != null)
					return nullity.isNon_null();
			}
		}
		return false;
	}
	public boolean isDeclaredMonoNonNull() {
		FieldBinding field = getFieldBinding();
		
		if (field == null)
			return false;
		if (Nullity.isPrimitiveType(field.type))
			return false;
		
		FieldDeclaration fieldDeclaration = getFieldDeclaration(field);
		if (fieldDeclaration != null) {
			if (field.isFinal() && fieldDeclaration.initialization != null )
				return fieldDeclaration.initialization.isDeclaredNonNull();
			if (fieldDeclaration.type instanceof JmlTypeReference) {
				Nullity nullity = ((JmlTypeReference)fieldDeclaration.type).getNullity();
				if (nullity != null)
					return nullity.isMono_non_null();
			}
		}
		return false;
	}

	static FieldDeclaration getFieldDeclaration(FieldBinding fieldBinding) {
		FieldDeclaration result;
		if (null != (result = fieldBinding.fieldDeclaration))
			return result;
		if ((fieldBinding.declaringClass instanceof BinaryTypeBinding)) {
			BinaryTypeBinding binaryTypeBinding = (BinaryTypeBinding) fieldBinding.declaringClass;
			return JmlBinaryLookup.getDeclaration(fieldBinding, binaryTypeBinding);
		}
		return null;
	}

	public boolean isPrimitiveType() {
		FieldBinding field = getFieldBinding();
	
		if (field != null)
			return Nullity.isPrimitiveType(field.type);
		return true;
	}

	private FieldBinding getFieldBinding() {
		FieldBinding field;
		if (this.otherBindings == null) {
			if (this.binding instanceof FieldBinding) {
				field = (FieldBinding) this.binding;
			} else {
				field = null;
			}
		} else {
			field = this.otherBindings[this.otherBindings.length-1];
		}
		
		return field;
	}
		
	protected void generateTestForNullity(BlockScope currentScope, CodeStream codeStream) {
		if (! isPrimitiveType()  
		 && (this.isDeclaredNonNull() || this.isDeclaredMonoNonNull())){
		   JmlCastExpression.generateTestForNullity(currentScope, codeStream, "qualified field '"+this.toString()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		}
	}

	public void checkNPE(BlockScope scope, FlowContext flowContext, FlowInfo flowInfo, boolean checkString) {
		super.checkNPE(scope, flowContext, flowInfo, checkString);
		if (!scope.compilerOptions().useNonNullTypeSystem())
			return;
		AbstractVariableDeclaration receiverDecl = null; 
		boolean isKnownToBeNonNull = false;
		if  ((this.bits & ASTNode.RestrictiveFlagMASK) == Binding.FIELD) {
			receiverDecl = ((FieldBinding)this.binding).fieldDeclaration;
		} else {
			LocalVariableBinding localBinding = (LocalVariableBinding)this.binding;
			if (localBinding != null) {
				receiverDecl = localBinding.declaration;
				isKnownToBeNonNull = flowInfo.isDefinitelyNonNull(localBinding);
			}
		}	
		if (!isKnownToBeNonNull && receiverDecl != null && receiverDecl.type != null && !receiverDecl.type.isDeclaredNonNull()) {
			scope.problemReporter().attemptToDereferenceNullValue(this);
		}
		int length = this.otherBindings == null ? 0 : otherBindings.length;
		for (int i = 0; i < length-1; i++) {
			FieldDeclaration fieldDecl = otherBindings[i].fieldDeclaration;
			if (fieldDecl == null || fieldDecl.type == null) {
				// FIXME: complain?
				continue;
			}
			if (!fieldDecl.type.isDeclaredNonNull()) {
				scope.problemReporter().attemptToDereferenceNullValue(this, 1+i+this.indexOfFirstFieldBinding);
			}
		}
	}
}
