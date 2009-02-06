/**
 * 
 */
package org.jmlspecs.jml4.fspv.theory;

/**
 * @author karabot
 *
 */
public class TheoryUnaryExpression extends TheoryExpression {

	public TheoryUnaryExpression(TheoryType type) {
		super(type);
		// TODO Auto-generated constructor stub
	}

	//TODO: Add content
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
}
