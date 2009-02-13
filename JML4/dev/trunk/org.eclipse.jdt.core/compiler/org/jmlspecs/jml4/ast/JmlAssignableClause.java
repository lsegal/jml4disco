package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlAssignableClause extends JmlClause {

	//@ invariant this.expr != null;
	
	// expr could be a JmlKeyword, or a single argument to the clause.
	public JmlAssignableClause(JmlIdentifier keyword, Expression expr) {
		super(keyword, expr);
	}

	public JmlAssignableClause(JmlIdentifier keyword, JmlStoreRefListExpression expr) {
		super(keyword, expr);
	}

	protected TypeBinding resolveType(BlockScope scope) {
		if (!hasNonKeywordExpr())
			return null;
		JmlStoreRefListExpression storeRefList = getStoreRefs();
		return storeRefList.resolveType(scope);
	}

	//@ requires this.expr instanceof JmlStoreRefListExpression
	private JmlStoreRefListExpression getStoreRefs() {
		return (JmlStoreRefListExpression) this.expr;
	}
	
	private /*@pure*/ boolean admissibleExprAST() {
		return this.expr == JmlKeywordExpression.EVERYTHING
		|| this.expr == JmlKeywordExpression.NOT_SPECIFIED
		|| this.expr == JmlKeywordExpression.NOTHING
		|| this.expr instanceof JmlStoreRefListExpression;
	}
}
