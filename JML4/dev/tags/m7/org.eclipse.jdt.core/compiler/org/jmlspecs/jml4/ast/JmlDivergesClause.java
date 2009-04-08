package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlDivergesClause extends JmlClause {
	//@ public invariant this.expr != null;

	public JmlDivergesClause(JmlIdentifier keyword, Expression predOrKeyword) {
		super(keyword, predOrKeyword);
	}
}
