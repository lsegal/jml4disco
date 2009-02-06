package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.JmlAllRangeExpression;
import org.eclipse.jdt.internal.compiler.ast.ArrayReference;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.JmlRangeExpression;

public class JmlRangeArrayReference extends ArrayReference {

	public JmlRangeArrayReference(Expression rec, Expression lo, Expression hi) {
		super(rec, new JmlRangeExpression(lo, hi));
	}
	
	public JmlRangeArrayReference(Expression rec, JmlAllRangeExpression are) {
		super(rec, are);
	}
}
