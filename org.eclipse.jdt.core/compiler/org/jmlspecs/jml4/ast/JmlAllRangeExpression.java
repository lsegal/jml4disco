package org.jmlspecs.jml4.ast;


public class JmlAllRangeExpression extends JmlArrayIndexRangeExpression {

	private boolean rangeResolved;
	
	public JmlAllRangeExpression() {
		super(null, null);
		this.rangeResolved = false;
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		output.append("*"); //$NON-NLS-1$
		if (this.rangeResolved) {
//			output.append("("); //$NON-NLS-1$
//			output.append(this.low);
//			output.append(".."); //$NON-NLS-1$
//			output.append(this.high);
//			output.append(")"); //$NON-NLS-1$
		}
		return output;
	}
}
