package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlRequiresClause extends JmlClause {

	//@ public invariant this.expr != null;
	
	public JmlRequiresClause(JmlIdentifier keyword, Expression predOrKeyword) {
		super(keyword, predOrKeyword);
	}

	public String kind() {
		return "precondition"; //$NON-NLS-1$
	}

	public void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		// FIXME: handle case where clause argument is \same (?).
		if (!hasNonKeywordExpr())
			return;
		
		if (DEBUG)
			generatePrintValue(currentScope, methodDecl, codeStream);
		generateInvariantCheck(currentScope, methodDecl, codeStream);
		generateEvaluateAndThrowIfFalse(currentScope, codeStream);
	}
}