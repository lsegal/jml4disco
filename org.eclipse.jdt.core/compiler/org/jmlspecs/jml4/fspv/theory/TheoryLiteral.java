/**
 * 
 */
package org.jmlspecs.jml4.fspv.theory;

/**
 * @author karabot
 *
 */
public class TheoryLiteral extends TheoryExpression {

	public static final String ZERO = "0"; //$NON-NLS-1$
	public static final String	TRUE	= "True"; //$NON-NLS-1$
	public static final String	FALSE	= "False"; //$NON-NLS-1$
	public final String	value;

	public TheoryLiteral(String value, TheoryType type) {
		super(type);
		this.value = value;
	}

	public String toString() {
		return this.value;
	}

	public String toStringWithType() {
		return this.value + TheoryType.TYPE_SEPARATOR + this.type;
	}

	public static TheoryLiteral True() {
		return new TheoryLiteral(TheoryLiteral.TRUE, TheoryType.Bool());
	}

	public static TheoryLiteral False() {
		return new TheoryLiteral(TheoryLiteral.FALSE, TheoryType.Bool());
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}

	public static TheoryExpression Zero(TheoryType type) {
		return new TheoryLiteral(ZERO, type);
	}

}
