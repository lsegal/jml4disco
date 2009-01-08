package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ArrayAllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.ArrayInitializer;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlFieldDeclaration extends FieldDeclaration {

	public /*@nullable*/ JmlDataGroupClause[] dataGroups;
	public JmlFieldDeclaration() {
		// for subtypes or conversion
	}

	public JmlFieldDeclaration(char[] name, int sourceStart, int sourceEnd) {
		super(name, sourceStart, sourceEnd);
	}

	public FlowInfo analyseCode(MethodScope initializationScope, FlowContext flowContext, FlowInfo flowInfo) {
		//Set nullity for field through its annotations
		if (initializationScope.compilerOptions().useNonNullTypeSystem()) {
			if (this.annotations != null && type!=null) {
				type.handleAnnotations(this.annotations, initializationScope.problemReporter());
			}
		}
		FlowInfo fromSuper = super.analyseCode(initializationScope, flowContext, flowInfo); 
		// TODO: remove the following test once we fix the parser to only use
		// JML AST Nodes when EnabledJml.
		if (initializationScope.compilerOptions().useNonNullTypeSystem()) {
			if (this.type != null) {
				if (this.type.isDeclaredNonNull() || this.type.isDeclaredMonoNonNull()) {
					if (this.initialization != null && !this.initialization.isDeclaredNonNull()) {
						initializationScope.problemReporter().attemptToAssignNullValue(this);
					}
				}
				if (this.initialization != null && this.type instanceof JmlArrayTypeReference) {
					JmlArrayTypeReference aType = (JmlArrayTypeReference) this.type;
					Nullity[] elemNullities = aType.elemNullities;
					//FIXME: generalize for more than 1 dim
					if (elemNullities != null && this.initialization instanceof ArrayAllocationExpression) {
						ArrayInitializer arrayInit = ((ArrayAllocationExpression) this.initialization).initializer;
						if (arrayInit != null) {
							Expression[] elems = arrayInit.expressions;
							if (elems != null && elemNullities[0].isNon_null()) {
								for (int i = 0; i < elems.length; i++) {
									if (!elems[i].isDeclaredNonNull()) {
										initializationScope.problemReporter().attemptToAssignNullValue(this);
									}
								}
							}
						}
					}
				}
			}
		}
		return fromSuper;
	}

	protected void generateTestForNullity(BlockScope currentScope, CodeStream codeStream) {
		if (this.type != null && this.binding != null  && ! Nullity.isPrimitiveType(this.binding.type) 
		 && (this.type.isDeclaredNonNull() || this.type.isDeclaredMonoNonNull())) {
		   JmlCastExpression.generateTestForNullity(currentScope, codeStream, "field (2) "+(new String(this.name))); //$NON-NLS-1$
		}
	}
	protected void generateTestForNullityUninitedConst(BlockScope currentScope,
			CodeStream codeStream) {
		if (this.initialization == null && this.binding.constant() != Constant.NotAConstant) {
			   codeStream.aconst_null();
			   generateTestForNullity(currentScope, codeStream);
			}
	}

	public StringBuffer printStatement(int indent, StringBuffer output) {
		super.printStatement(indent, output);
		return printDataGroups(indent, output);
	}

	private StringBuffer printDataGroups(int indent, StringBuffer output) {
		int length = (this.dataGroups == null ? 0 : this.dataGroups.length);
		for (int i = 0; i < length; i++) {
			dataGroups[i].print(indent, output);
		}
		return output;
	}

	public StringBuffer printAsExpression(int indent, StringBuffer output) {
		super.printAsExpression(indent, output);
		return printDataGroups(indent, output);
	}

	public StringBuffer print(int indent, StringBuffer output) {
		super.print(indent, output);
		return printDataGroups(indent, output);
	}

}