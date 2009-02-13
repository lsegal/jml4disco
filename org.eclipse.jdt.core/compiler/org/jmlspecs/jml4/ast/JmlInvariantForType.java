package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ExtraCompilerModifiers;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlInvariantForType extends JmlTypeBodyDeclaration {
    
	public static final JmlInvariantForType[] EMPTY_INVARIANT_ARRAY = new JmlInvariantForType[0];
	
    private static final int VALID_MODIFIERS = ExtraCompilerModifiers.AccVisibilityMASK | ClassFileConstants.AccStatic;
    private static final String VALID_MODIFIER_LIST = "public, protected, private & static"; //$NON-NLS-1$

    public JmlInvariantForType(JmlIdentifier clauseKeyword, Expression pred) {
		super(clauseKeyword, pred);
	}

	public void resolve(BlockScope staticInitializerScope, BlockScope initializerScope) {
		resolve(isStatic ? staticInitializerScope : initializerScope);
	}

	public FlowInfo analyseCode(BlockScope staticInitializerScope, BlockScope initializerScope, FlowContext context, FlowInfo flowInfo) {
		final BlockScope scope = (isStatic ? staticInitializerScope : initializerScope);
		checkModifiers(scope, VALID_MODIFIERS, VALID_MODIFIER_LIST);
		return expr.analyseCode(scope, context, flowInfo);
	}

	public void generateCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		if (DEBUG) {
			generatePrintValue(currentScope, methodDecl, codeStream);
		}
		generateEvaluateAndThrowIfFalse(currentScope, codeStream);
	}
}
