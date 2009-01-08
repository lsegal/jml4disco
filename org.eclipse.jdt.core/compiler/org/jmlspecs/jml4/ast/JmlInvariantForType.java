package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ExtraCompilerModifiers;

public class JmlInvariantForType extends JmlTypeBodyDeclaration {
    private static final int VALID_MODIFIERS = ExtraCompilerModifiers.AccVisibilityMASK | ClassFileConstants.AccStatic;
    private static final String VALID_MODIFIER_LIST = "public, protected, private & static"; //$NON-NLS-1$
    
    // TODO: correctly support static instances of this clause.
	private final boolean isStatic = false;
	
	public JmlInvariantForType(String clauseKeyword, boolean isRedundant, Expression pred) {
		super(clauseKeyword, isRedundant, pred);
	}

	public String kind() {
		return "invariant"; //$NON-NLS-1$
	}
	
	public StringBuffer print(int indent, StringBuffer output) {
		// FIXME: also need to print the modifiers
		return super.print(indent, output);
	}

	public void resolve(BlockScope staticInitializerScope, BlockScope initializerScope) {
		super.resolve(isStatic ? staticInitializerScope : initializerScope);
	}

	public FlowInfo analyseCode(BlockScope staticInitializerScope, BlockScope initializerScope, FlowContext context, FlowInfo flowInfo) {
		final BlockScope scope = (isStatic ? staticInitializerScope : initializerScope);
		checkModifiers(scope, VALID_MODIFIERS, VALID_MODIFIER_LIST);
		return pred.analyseCode(scope, context, flowInfo);
	}

	public void generateCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		if (DEBUG) {
			generatePrintValue(currentScope, methodDecl, codeStream);
		}
		generateEvaluateAndThrowIfFalse(currentScope, codeStream);
	}
}
