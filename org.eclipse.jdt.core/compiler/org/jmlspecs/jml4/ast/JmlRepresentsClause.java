package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ExtraCompilerModifiers;

public class JmlRepresentsClause extends JmlTypeBodyDeclaration {
    public static final String KEYWORD_AS_STRING = "represents"; //$NON-NLS-1$
	private static final int VALID_MODIFIERS = ExtraCompilerModifiers.AccVisibilityMASK | ClassFileConstants.AccStatic;
	// TODO: consider generating the following string from VALID_MODIFIERS instead ...
    private static final String VALID_MODIFIER_LIST = "public, protected, private & static"; //$NON-NLS-1$

    // WARNING: beware that we will eventually support both the functional and
	// relational forms of this clause. When that happens, it might be worth
	// storing both the functional and relational form expressions in expr
	// (even though the relational form expression will be a predicate that
	// could be stored in super.pred.
    
    public final JmlStoreRef storeRef;
    public final Expression expr;

    // TODO: correctly support static instances of this clause.
	private final boolean isStatic = false;
	
	public JmlRepresentsClause(boolean isRedundant, JmlStoreRef storeRef, Expression expr) {
		super(KEYWORD_AS_STRING, isRedundant);
		this.storeRef = storeRef;
		this.expr = expr;
	}

	public String kind() {
		return KEYWORD_AS_STRING;
	}
	
	public StringBuffer print(int indent, StringBuffer output) {
		output.append(this.clauseKeyword + SPACE);
		storeRef.print(indent, output);
		output.append(" = "); //$NON-NLS-1$
		expr.print(indent, output);
		return output.append(SEMICOLON);
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
}
