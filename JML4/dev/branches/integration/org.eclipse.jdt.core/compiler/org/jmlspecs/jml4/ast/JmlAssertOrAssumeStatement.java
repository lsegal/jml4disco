package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AssertStatement;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.jmlspecs.jml4.compiler.JmlConstants;

public class JmlAssertOrAssumeStatement extends AssertStatement {

	public final String lexeme;

	public JmlAssertOrAssumeStatement(String lexeme, Expression exceptionArgument,
			Expression assertExpression, int startPosition) {
		super(exceptionArgument, assertExpression, startPosition);
		this.lexeme = lexeme;
	}

	public JmlAssertOrAssumeStatement(String lexeme, Expression assertExpression,
			int startPosition) {
		super(assertExpression, startPosition);
		this.lexeme = lexeme;
	}

	public void resolve(BlockScope scope) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.RESOLVE)
			return;
		super.resolve(scope);
	}

	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_ANALYSIS)
			return flowInfo;
		return super.analyseCode(currentScope, flowContext, flowInfo);
	}

	public void generateCode(BlockScope currentScope, CodeStream codeStream) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_GENERATION)
			return;
		if (currentScope.compilerOptions().jmlRacEnabled)
			// FIXME: current we use Java asserts, but this is only a temporary solution.
			super.generateCode(currentScope, codeStream);
	}

}