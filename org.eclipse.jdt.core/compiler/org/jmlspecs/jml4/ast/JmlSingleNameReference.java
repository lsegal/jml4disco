package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.SingleNameReference;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlSingleNameReference extends SingleNameReference {

	public JmlSingleNameReference(char[] source, long pos) {
		super(source, pos);
	}
	public int nullStatus(FlowInfo flowInfo) {
		if (this.isDeclaredNonNull())
			return FlowInfo.NON_NULL;
		else
			return super.nullStatus(flowInfo);
/*		if (this.constant != null && this.constant != Constant.NotAConstant) {
			return FlowInfo.NON_NULL; // constant expression cannot be null
		}
		if (this.isDeclaredNonNull())
			   return FlowInfo.NON_NULL;
		if ((bits & RestrictiveFlagMASK) == Binding.LOCAL) { // reading a local variable
			LocalVariableBinding local = (LocalVariableBinding) this.binding;
			if (local != null) {
				if (flowInfo.isDefinitelyNull(local))
					return FlowInfo.NULL;
				if (flowInfo.isDefinitelyNonNull(local))
					return FlowInfo.NON_NULL;
				return FlowInfo.UNKNOWN;
			}
		}
		return FlowInfo.UNKNOWN; // never get there 
*/
	}
	public boolean isDeclaredNonNull() {
		switch (this.bits & ASTNode.RestrictiveFlagMASK) {
		case Binding.FIELD : // reading a field
			FieldBinding field = (FieldBinding) this.binding;
			if (field == null)
				return false;
			if (Nullity.isPrimitiveType(field.type))
				return true;
			FieldDeclaration fieldDeclaration = JmlQualifiedNameReference.getFieldDeclaration(field);
			if (fieldDeclaration != null) {
				if (field.isFinal() && fieldDeclaration.initialization != null )
					return fieldDeclaration.initialization.isDeclaredNonNull();
				if (fieldDeclaration.type instanceof JmlTypeReference)
					return ((JmlTypeReference)fieldDeclaration.type).isDeclaredNonNull();
			}
			return false;
		case Binding.LOCAL : // reading a local variable
			LocalVariableBinding local = (LocalVariableBinding) this.binding;
			if (local == null)
				return false;
			if (Nullity.isPrimitiveType(local.type))
				return true;
			return (local.declaration.type instanceof JmlTypeReference 
			   &&  ((JmlTypeReference)local.declaration.type).getNullity().isNon_null());
		}
		//@ assert false;
		return false; // never get there 
	}
	public boolean isDeclaredMonoNonNull() {
		switch (this.bits & ASTNode.RestrictiveFlagMASK) {
		case Binding.FIELD : // reading a field
			FieldBinding field = (FieldBinding) this.binding;
			if (field == null)
				return false;
			if (Nullity.isPrimitiveType(field.type))
				return false;
			FieldDeclaration fieldDeclaration = JmlQualifiedNameReference.getFieldDeclaration(field);
			if (fieldDeclaration != null) {
				if (fieldDeclaration.type instanceof JmlTypeReference)
					return ((JmlTypeReference)fieldDeclaration.type).isDeclaredMonoNonNull();
			}
			return false;
		case Binding.LOCAL : // reading a local variable
			LocalVariableBinding local = (LocalVariableBinding) this.binding;
			if (local == null)
				return false;
			if (Nullity.isPrimitiveType(local.type))
				return false;
			return (local.declaration.type instanceof JmlTypeReference 
			   &&  ((JmlTypeReference)local.declaration.type).getNullity().isMono_non_null());
		}
		//@ assert false;
		return false; // never get there 
	}
	
	protected void generateTestForNullityField(BlockScope currentScope,
			CodeStream codeStream, TypeBinding resolvedType) {
		if (! Nullity.isPrimitiveType(resolvedType))
			   generateTestForNullity(currentScope, codeStream, "field (snr) "); //$NON-NLS-1$
	}

	protected void generateTestForNullityLocal(BlockScope currentScope,
			CodeStream codeStream) {
		generateTestForNullity(currentScope, codeStream, "local (snr) "); //$NON-NLS-1$
	}
	
	private void generateTestForNullity(BlockScope currentScope, CodeStream codeStream, String msg) {
		if (isDeclaredNonNull() || isDeclaredMonoNonNull())
		   JmlCastExpression.generateTestForNullity(currentScope, codeStream, msg+" '"+(new String(this.token))+"'"); //$NON-NLS-1$ //$NON-NLS-2$
	}
}
