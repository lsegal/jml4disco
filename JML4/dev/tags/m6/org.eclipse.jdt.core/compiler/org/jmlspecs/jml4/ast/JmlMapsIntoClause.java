package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlMapsIntoClause extends JmlClause implements JmlDataGroupClause {
	
	public final Expression[] groupNames;
	
	public JmlMapsIntoClause(JmlIdentifier clauseKeyword, Expression mapstoExprRef, Expression[] groupNames) {
		super(clauseKeyword, mapstoExprRef);
		this.groupNames = groupNames;
	}

	public void resolve(BlockScope scope) {
		super.resolve(scope);
		for (int i = 0; i < this.groupNames.length; i++) {
			this.groupNames[i].resolve(scope);
		}
	}

	protected StringBuffer printClauseContent(StringBuffer output) {
		super.printClauseContent(output);
		output.append(" \\into "); //$NON-NLS-1$
		for (int i = 0; i < this.groupNames.length; i++) {
			if (i>0)
				output.append(", "); //$NON-NLS-1$
			this.groupNames[i].print(0, output);
		}
		return output;
	}

}
