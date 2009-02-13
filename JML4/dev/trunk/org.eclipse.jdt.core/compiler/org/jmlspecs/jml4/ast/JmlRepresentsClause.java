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

public class JmlRepresentsClause extends JmlTypeBodyDeclaration {
	
	public static final JmlRepresentsClause[] EMPTY_REPRESENTS_ARRAY = new JmlRepresentsClause[0];

    public static final char[] KEYWORD = "represents".toCharArray(); //$NON-NLS-1$
	private static final int VALID_MODIFIERS = ExtraCompilerModifiers.AccVisibilityMASK | ClassFileConstants.AccStatic;
	// TODO: consider generating the following string from VALID_MODIFIERS instead ...
    private static final String VALID_MODIFIER_LIST = "public, protected, private & static"; //$NON-NLS-1$

	//@ public invariant this.expr != null;
    public final Expression storeRef;

    public JmlRepresentsClause(JmlIdentifier clauseKeyword, Expression storeRef, Expression expr) {
		super(clauseKeyword, expr);
		this.storeRef = storeRef;
	}

	public void resolve(BlockScope staticInitializerScope, BlockScope initializerScope) {
		// FIXME: not fully implemented
		super.resolve(isStatic ? staticInitializerScope : initializerScope);
	}

	public FlowInfo analyseCode(BlockScope staticInitializerScope, BlockScope initializerScope, FlowContext context, FlowInfo flowInfo) {
		// FIXME: not fully implemented
		final BlockScope scope = (isStatic ? staticInitializerScope : initializerScope);
		checkModifiers(scope, VALID_MODIFIERS, VALID_MODIFIER_LIST);
		return expr.analyseCode(scope, context, flowInfo);
	}

	public void generateCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		// FIXME: what to do here?
	}

	protected StringBuffer printClauseContent(StringBuffer output) {
		this.storeRef.print(0, output).append(" = "); //$NON-NLS-1$
		return super.printClauseContent(output);
	}
}
