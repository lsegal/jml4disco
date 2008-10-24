/**
 * 
 */
package org.jmlspecs.jml4.fspv.theory;

/**
 * @author karabot
 *
 */
public class TheoryOperator {

	private static final String	EQUAL	= "="; //$NON-NLS-1$
	private static final String	LESS_EQUAL	= "\\<le>"; //$NON-NLS-1$
	private static final String	GREATER_EQUAL	= "\\<ge>"; //$NON-NLS-1$
	private static final String	NOT_EQUAL	= "\\<noteq>"; //$NON-NLS-1$
	private static final String	OR_OR	= "\\<or>";  //$NON-NLS-1$ //FIXME: Map to a conditional OR
	private static final String	AND_AND	= "\\<and>"; //$NON-NLS-1$ //FIXME: Map to a condition AND
	private static final String	PLUS	= "+";  //$NON-NLS-1$
	private static final String	MINUS	= "-"; //$NON-NLS-1$
	private static final String	NOT	= "\\<not>"; //$NON-NLS-1$
	private static final String	REMAINDER	= "mod"; //$NON-NLS-1$
	private static final String	AND	= "\\<and>"; //$NON-NLS-1$
	private static final String	MULTIPLY	= "*"; //$NON-NLS-1$
	private static final String	OR	= "\\<or>"; //$NON-NLS-1$
	private static final String	DIVIDE	= "div"; //$NON-NLS-1$
	private static final String	GREATER	= ">"; //$NON-NLS-1$
	private static final String	LESS	= "<"; //$NON-NLS-1$
	private static final String	QUESTION_COLON	= "?:"; //$NON-NLS-1$ //FIXME: Maybe should consider 
	private String	op;
	
	private TheoryOperator(String op) {
		this.op=op;
	}

	public static TheoryOperator Equal() {
		return new TheoryOperator(EQUAL);
	}

	public static TheoryOperator LessEqual() {
		return new TheoryOperator(LESS_EQUAL);
	}

	public static TheoryOperator GreaterEqual() {
		return new TheoryOperator(GREATER_EQUAL);
	}

	public static TheoryOperator NotEqual() {
		return new TheoryOperator(NOT_EQUAL);
	}

	public static TheoryOperator OrOr() {
		return new TheoryOperator(OR_OR);
	}

	public static TheoryOperator AndAnd() {
		return new TheoryOperator(AND_AND);
	}

	public static TheoryOperator Plus() {
		return new TheoryOperator(PLUS);
	}

	public static TheoryOperator Minus() {
		return new TheoryOperator(MINUS);
	}

	public static TheoryOperator Not() {
		return new TheoryOperator(NOT);
	}

	public static TheoryOperator Remainder() {
		return new TheoryOperator(REMAINDER);
	}

	public static TheoryOperator And() {
		return new TheoryOperator(AND);
	}

	public static TheoryOperator Multiply() {
		return new TheoryOperator(MULTIPLY);
	}

	public static TheoryOperator Or() {
		return new TheoryOperator(OR);
	}

	public static TheoryOperator Divide() {
		return new TheoryOperator(DIVIDE);
	}

	public static TheoryOperator Greater() {
		return new TheoryOperator(GREATER);
	}

	public static TheoryOperator Less() {
		return new TheoryOperator(LESS);
	}

	public static TheoryOperator QuestionColon() {
		return new TheoryOperator(QUESTION_COLON);
	}

	public String toString() {
		return(this.op);
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}

	
}
