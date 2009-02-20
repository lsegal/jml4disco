package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.jmlspecs.jml4.compiler.JmlConstants;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlSignalsClause extends JmlClause {

	public final Argument arg;
	
	public JmlSignalsClause(JmlIdentifier clauseKeyword,
			Argument arg, 
			/*@nullable*/Expression predOrKeyword) {
		super(clauseKeyword, predOrKeyword);
		this.arg = arg;
	}

	public void resolve(BlockScope scope) {
		BlockScope scopeWithArg = new BlockScope(scope);
		this.arg.resolveForCatch(scopeWithArg);
		if (hasNonKeywordExpr()) {
			resolveType(scopeWithArg);
		}
	}

	protected StringBuffer printClauseContent(StringBuffer output) {
		output.append('(');
		if (arg.name != JmlConstants.JML_ANON)
			this.arg.print(0, output);
		else
			output.append(this.arg.type);
		output.append(')');
		if(this.hasExpr())
			output.append(SPACE);
		return super.printClauseContent(output);
	}

}
