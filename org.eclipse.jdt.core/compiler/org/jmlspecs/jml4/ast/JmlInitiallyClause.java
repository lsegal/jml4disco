package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ExtraCompilerModifiers;

public class JmlInitiallyClause extends JmlTypeBodyDeclaration {
    private static final int VALID_MODIFIERS = ExtraCompilerModifiers.AccVisibilityMASK;
    private static final String VALID_MODIFIER_LIST = "public, protected & private"; //$NON-NLS-1$

	public JmlInitiallyClause(String clauseKeyword, Expression pred) {
		super(clauseKeyword, false, pred); // initially cannot be redundant in current JML grammar
	}

	public String kind() {
		return "initially"; //$NON-NLS-1$
	}
	
	public StringBuffer print(int indent, StringBuffer output) {
		// FIXME: also need to print the modifiers
		return super.print(indent, output);
	}

	public void resolve(BlockScope staticInitializerScope, BlockScope initializerScope) {
		super.resolve(initializerScope);
	}

	public FlowInfo analyseCode(BlockScope staticInitializerScope, BlockScope initializerScope, FlowContext context, FlowInfo flowInfo) {
		checkModifiers(initializerScope, VALID_MODIFIERS, VALID_MODIFIER_LIST);
		return pred.analyseCode(initializerScope, context, flowInfo);
	}

	public void generateCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		if (DEBUG) {
			generatePrintValue(currentScope, methodDecl, codeStream);
		}
		generateEvaluateAndThrowIfFalse(currentScope, codeStream);
	}
}
