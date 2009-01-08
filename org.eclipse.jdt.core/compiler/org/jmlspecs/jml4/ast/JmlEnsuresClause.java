package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

public class JmlEnsuresClause extends JmlClause {

	public JmlEnsuresClause(String keyword, boolean isRedundant, Expression pred) {
		super(keyword, isRedundant, pred);
	}

	public JmlEnsuresClause(String keyword, boolean isRedundant) {
		super(keyword, isRedundant);
	}

	public String kind() {
		return "postcondition"; //$NON-NLS-1$
	}

	public StringBuffer print(int indent, StringBuffer output) {
		output.append(this.clauseKeyword + SPACE);
		if (hasPred()) {
			this.pred.print(indent, output);
		} else {
			output.append("\\not_specified"); //$NON-NLS-1$
		}
		return output.append(SEMICOLON);
	}

	public void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		if (!hasPred())
			return;
		final JmlLocalDeclaration result = (methodDecl instanceof JmlMethodDeclaration)
											? ((JmlMethodDeclaration) methodDecl).resultValue
											: null;
		if (DEBUG)
			if (result != null)
				generatePrintValue(currentScope, methodDecl, codeStream, result.binding, "result"); //$NON-NLS-1$
		if (DEBUG)
			generatePrintValue(currentScope, methodDecl, codeStream);
		generateInvariantCheck(currentScope, methodDecl, codeStream);
		generateEvaluateAndThrowIfFalse(currentScope, codeStream);
	}
}
