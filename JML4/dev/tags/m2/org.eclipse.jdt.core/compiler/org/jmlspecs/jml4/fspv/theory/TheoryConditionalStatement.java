/**
 * 
 */
package org.jmlspecs.jml4.fspv.theory;

/**
 * @author karabot
 *
 */
public class TheoryConditionalStatement extends TheoryStatement {
	public final TheoryExpression condition;
	public final TheoryBlockStatement thenBlock;
	public final TheoryBlockStatement elseBlock;
	public TheoryConditionalStatement(TheoryExpression condition,
			TheoryBlockStatement thenBlock, TheoryBlockStatement elseBlock) {
		this.condition = condition;
		this.thenBlock = thenBlock;
		this.elseBlock = elseBlock;
	}

	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
}
