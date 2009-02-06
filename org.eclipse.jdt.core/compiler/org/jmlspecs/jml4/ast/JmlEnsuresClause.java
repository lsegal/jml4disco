package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlEnsuresClause extends JmlClause {

	//@ public invariant this.expr != null;

	public JmlEnsuresClause(JmlIdentifier keyword, Expression predOrKeyword) {
		super(keyword, predOrKeyword);
	}

	// FIXME: is this really much better than "ensures clause"?  What is it is a _redundantly variant?
	public String kind() {
		return "postcondition"; //$NON-NLS-1$
	}

	public void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		if (!hasNonKeywordExpr())
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
