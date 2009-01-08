package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AssertStatement;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

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

	public void generateCode(BlockScope currentScope, CodeStream codeStream) {
		if (currentScope.compilerOptions().jmlRacEnabled)
			// FIXME: current we use Java asserts, but this is only a temporary solution.
			super.generateCode(currentScope, codeStream);
	}

}