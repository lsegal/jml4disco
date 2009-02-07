package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ExtraCompilerModifiers;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlInitiallyClause extends JmlTypeBodyDeclaration {

	public static final JmlInitiallyClause[] EMPTY_INITIALLY_ARRAY = new JmlInitiallyClause[0];

	private static final int VALID_MODIFIERS = ExtraCompilerModifiers.AccVisibilityMASK;
    private static final String VALID_MODIFIER_LIST = "public, protected & private"; //$NON-NLS-1$

    public JmlInitiallyClause(JmlIdentifier clauseKeyword, Expression expr) {
		super(clauseKeyword, expr);
	}

	public void resolve(BlockScope staticInitializerScope, BlockScope initializerScope) {
		super.resolve(initializerScope);
	}

	public FlowInfo analyseCode(BlockScope staticInitializerScope, BlockScope initializerScope, FlowContext context, FlowInfo flowInfo) {
		checkModifiers(initializerScope, VALID_MODIFIERS, VALID_MODIFIER_LIST);
		return expr.analyseCode(initializerScope, context, flowInfo);
	}

	public void generateCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		if (DEBUG) {
			generatePrintValue(currentScope, methodDecl, codeStream);
		}
		generateEvaluateAndThrowIfFalse(currentScope, codeStream);
	}
}
