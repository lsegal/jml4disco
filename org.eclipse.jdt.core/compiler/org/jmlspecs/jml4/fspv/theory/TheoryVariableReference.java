/**
 * 
 */
package org.jmlspecs.jml4.fspv.theory;

/**
 * @author karabot
 *
 */
public class TheoryVariableReference extends TheoryExpression {
	public final TheoryVariable variable;

	public TheoryVariableReference(TheoryVariable variable) {
		super(variable.type);
		this.variable = variable;
	}
	
	public String toString() {
		return this.variable.getDecoratedName();
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
}
