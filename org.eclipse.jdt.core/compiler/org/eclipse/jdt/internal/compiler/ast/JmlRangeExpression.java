package org.eclipse.jdt.internal.compiler.ast;

public class JmlRangeExpression extends Expression {
	
	public /*@ nullable @*/ final Expression low;
	public /*@ nullable @*/ final Expression high;
	
	public JmlRangeExpression(/*@ nullable @*/ Expression lo, /*@ nullable @*/ Expression hi) {
		super();
		this.low = lo;
		this.high = hi;
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		output.append(this.low);
		output.append(".."); //$NON-NLS-1$
		output.append(this.high);
		return output;
	}

}
