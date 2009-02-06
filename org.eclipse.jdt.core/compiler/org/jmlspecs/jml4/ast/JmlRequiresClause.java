package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

public class JmlRequiresClause extends JmlClause {

	public final boolean isSame;
	//@ invariant isSame ==> pred == null;
	//@ pred != null ^ isSame ^ (* \not_specified *)
	
	//@ ensures this.clauseKeyword == clauseKeyword;
	//@ ensures this.pred == pred;
	//@ ensures this.isSame = false;
	public JmlRequiresClause(String clauseKeyword, boolean isRedundant, Expression pred) {
		super(clauseKeyword, isRedundant, pred);
		this.isSame = false;
	}

	//@ ensures this.clauseKeyword == clauseKeywordLexeme;
	//@ ensures this.pred == null;
	//@ ensures this.isSame == "\\same".equals(keywordGivenInsteadOfPred);
	public JmlRequiresClause(String clauseKeyword, boolean isRedundant, boolean isSame) {
		super(clauseKeyword, isRedundant);
		this.isSame = isSame;
	}

	public String kind() {
		return "precondition"; //$NON-NLS-1$
	}

	public StringBuffer print(int indent, StringBuffer output) {
		if (hasPred()) {
			return super.print(indent, output);
		} else {
			output.append(this.clauseKeyword + SPACE);
			if (isSame) {
				output.append("\\same"); //$NON-NLS-1$
			} else {
				output.append("\\not_specified"); //$NON-NLS-1$
			}
			return output.append(SEMICOLON);
		}
	}

	public void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		if (! hasPred())
			return;
		
		if (DEBUG)
			generatePrintValue(currentScope, methodDecl, codeStream);
		generateInvariantCheck(currentScope, methodDecl, codeStream);
		generateEvaluateAndThrowIfFalse(currentScope, codeStream);
	}
}