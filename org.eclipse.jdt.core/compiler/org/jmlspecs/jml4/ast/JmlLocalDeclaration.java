package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TagBits;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlLocalDeclaration extends LocalDeclaration {

	public JmlLocalDeclaration(char[] name, int sourceStart, int sourceEnd) {
		super(name, sourceStart, sourceEnd);
		if (this.type instanceof JmlTypeReference) {
			JmlTypeReference jmlType = (JmlTypeReference) this.type;
			if (jmlType.getNullity().hasDefaultNullity())
				jmlType.setNullity(Nullity.nullable_by_default);
		}
	}

	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		// this is in the constructor, so is it needed here too?
		// prj: yes!  Maybe it doesn't belong in the constructor...
		//set local nullity according to annotations
		if (currentScope.compilerOptions().useNonNullTypeSystem()) {
			if(this.annotations != null){
				this.type.handleAnnotations(this.annotations, currentScope.problemReporter());
			}
		}
		if (this.type instanceof JmlTypeReference) {
			JmlTypeReference jmlType = (JmlTypeReference) this.type;
			if (jmlType.getNullity().hasDefaultNullity())
				jmlType.setNullity(Nullity.nullable_by_default);
		}

		FlowInfo fromSuper = super.analyseCode(currentScope, flowContext, flowInfo);

		if (currentScope.compilerOptions().useNonNullTypeSystem()) {
			if (this.type != null && this.initialization != null)
				if (!Nullity.isAssignable(this.type, this.initialization, currentScope, flowContext, flowInfo)) {
					currentScope.problemReporter().attemptToAssignNullValue(this);
			}

			if (this.initialization != null && ((this.binding.type.tagBits & TagBits.IsBaseType) == 0)) {
				if (this.initialization.isDeclaredNonNull() || this.initialization.nullStatus(flowInfo) == FlowInfo.NON_NULL) { 
				    fromSuper.markAsDefinitelyNonNull(this.binding);
				} else if (fromSuper.isDefinitelyUnknown(this.binding)) {
						fromSuper.markAsPotentiallyNull(this.binding);
				}
			}
		}
		return fromSuper;
	}

	protected void generateTestForNullity(BlockScope currentScope, CodeStream codeStream) {
		if (! Nullity.isPrimitiveType(this.binding.type)  
		 && (this.type.isDeclaredNonNull() || this.type.isDeclaredMonoNonNull())) {
		   JmlCastExpression.generateTestForNullity(currentScope, codeStream, "local variable "+new String(this.name)); //$NON-NLS-1$
		}
	}
}