package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ArrayReference;
import org.eclipse.jdt.internal.compiler.ast.Expression;

public class DepricateJmlRangeArrayReference extends ArrayReference {

	public DepricateJmlRangeArrayReference(Expression rec, Expression lo, Expression hi) {
		super(rec, new JmlArrayIndexRangeExpression(lo, hi));
	}
	
	public DepricateJmlRangeArrayReference(Expression rec, JmlAllRangeExpression are) {
		super(rec, are);
	}
}
