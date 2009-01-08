package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BinaryTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.jmlspecs.jml4.lookup.JmlBinaryLookup;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlFieldReference extends FieldReference {

	private static final boolean DEBUG = false;
	public JmlFieldReference(char[] source, long pos) {
		super(source, pos);
	}
	public int nullStatus(FlowInfo flowInfo) {
		Nullity nullity = getNullity();
		if (nullity != null && nullity.isNon_null())
			return FlowInfo.NON_NULL;
		else if (this.binding.isFinal()) {
			FieldDeclaration fieldDecl = this.binding.fieldDeclaration;
			if (fieldDecl != null) {
               Expression init = fieldDecl.initialization;
               if (init != null && init.isDeclaredNonNull()) {
            	   return FlowInfo.NON_NULL;
               }
			}
		} else {
			if (DEBUG) System.out.println("field declaration's type isn't a JmlTypeReference"); //$NON-NLS-1$
		}
		return super.nullStatus(flowInfo);
	}

	public boolean isDeclaredNonNull() {
		Nullity nullity = getNullity();
		if (nullity != null && nullity.isNon_null())
			return true;
		FieldBinding fieldBinding = this.binding;
		if (fieldBinding != null) {
			FieldDeclaration fieldDeclaration = getFieldDeclaration(fieldBinding);
			if (fieldDeclaration != null) {
				if (fieldBinding.isFinal() && fieldDeclaration.initialization != null) 
					return fieldDeclaration.initialization.isDeclaredNonNull();
				if (fieldDeclaration.type instanceof JmlTypeReference) {
					// can we get here? isn't it covered in the getNullity case above?
					return ((JmlTypeReference) fieldDeclaration.type).isDeclaredNonNull();
				}
			}
		}
		return false;
	}
	public boolean isDeclaredMonoNonNull() {
		Nullity nullity = getNullity();
		return (nullity != null && nullity.isMono_non_null());
	}
	private FieldDeclaration getFieldDeclaration(FieldBinding fieldBinding) {
		FieldDeclaration result;
		if (null != (result = fieldBinding.fieldDeclaration))
			return result;
		if ((fieldBinding.declaringClass instanceof BinaryTypeBinding)) {
			BinaryTypeBinding binaryTypeBinding = (BinaryTypeBinding) fieldBinding.declaringClass;
			return JmlBinaryLookup.getDeclaration(fieldBinding, binaryTypeBinding);
		}
		return null;
	}
	private /*@ nullable */ Nullity getNullity() {
		if (this.binding == null)
			return null;
		FieldDeclaration field = this.binding.fieldDeclaration;
		if (field != null && field.type instanceof JmlTypeReference)
			return ((JmlTypeReference)field.type).getNullity();
		return null;
	}
	
	protected void generateTestForNullity(BlockScope currentScope, CodeStream codeStream) {
		if (! Nullity.isPrimitiveType(this.resolvedType)  
	     && (this.isDeclaredNonNull() || this.isDeclaredMonoNonNull()))
		   JmlCastExpression.generateTestForNullity(currentScope, codeStream, "field (1) "+this.toString()); //$NON-NLS-1$
	}
}
