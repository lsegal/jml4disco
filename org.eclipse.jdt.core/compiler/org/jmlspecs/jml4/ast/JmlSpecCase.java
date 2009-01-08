package org.jmlspecs.jml4.ast;

import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ExtraCompilerModifiers;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;

public class JmlSpecCase extends JmlAstNode {

    private static final int VALID_MODIFIERS = ExtraCompilerModifiers.AccVisibilityMASK;
	private static final int LIGHTWEIGHT = 0;
	private static final int BEHAVIOR = 1;
	private static final int NORMAL_BEHAVIOR = 2;
	private static final int EXCEPTIONAL_BEHAVIOR = 3;
	
	private final int kind;
	private final String behaviorKeywordLexeme;
	public final JmlSpecCaseBody body;
	private final int modifiers;
	//@ invariant (kind == LIGHTWEIGHT) ==> (modifiers == 0);
	
	//@ ensures this.kind == LIGHTWEIGHT;
	//@ ensures this.behaviorKeywordLexeme == "";
	//@ ensures this.body == body;
	//@ ensures this.modifiers == 0;
	public JmlSpecCase(JmlSpecCaseBody body) {
		this.kind = LIGHTWEIGHT;
		this.behaviorKeywordLexeme = ""; //$NON-NLS-1$
		this.body = body;
		this.modifiers = 0;
	}

	//@ ensures this.kind != LIGHTWEIGHT;
	//@ ensures this.behaviorKeywordLexeme == behaviorKeywordLexeme;
	//@ ensures this.body == body;
	public JmlSpecCase(String behaviorKeywordLexeme, JmlSpecCaseBody body, int modifiers) {
		this.kind = lexemeToKind(behaviorKeywordLexeme);
		this.behaviorKeywordLexeme = behaviorKeywordLexeme;
		this.body = body;
		this.modifiers = modifiers;
	}
	
	private static int lexemeToKind(String lexeme) {
		if (lexeme.equals("")) return LIGHTWEIGHT; //$NON-NLS-1$
		switch (lexeme.charAt(0)) {
			case 'b': return BEHAVIOR;
			case 'e': return EXCEPTIONAL_BEHAVIOR;
			case 'n': return NORMAL_BEHAVIOR;
			default:
				Assert.isTrue(false);
				return 0; // never reached
		}
	}

	public void resolve(MethodScope scope) {
		this.body.resolve(scope);
	}

	public StringBuffer print(int indent, StringBuffer output) {
		if (kind != LIGHTWEIGHT)
			output.append(this.behaviorKeywordLexeme + " "); //$NON-NLS-1$
		return this.body.print(indent,output);
	}

	// FIXME: check modifiers -- they should be valid.
	
	public void analysePostcondition(MethodScope scope, FlowContext methodContext, FlowInfo flowInfo) {
		this.body.analysePostcondition(scope, methodContext, flowInfo);
	}

	public void analysePrecondition(MethodScope scope, FlowContext methodContext, FlowInfo flowInfo) {
		this.body.analysePrecondition(scope, methodContext, flowInfo);
	}

	public void generateCheckOfPostcondition(BlockScope currentScope, AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		this.body.generateCheckOfPostcondition(currentScope, methodDeclaration, codeStream);
	}

	public void generateCheckOfPrecondition(MethodScope methodScope, AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		this.body.generateCheckOfPrecondition(methodScope, methodDeclaration, codeStream);
	}

	public List/*<Expression>*/ getRequiresExpressions() {
		return this.body.getRequiresExpressions();
	}

	public List/*<Expression>*/ getEnsuresExpressions() {
		return this.body.getEnsuresExpressions();
	}
}
