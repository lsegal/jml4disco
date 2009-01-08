/**
 * 
 */
package org.jmlspecs.jml4.fspv.theory;

/**
 * @author karabot
 *
 */
public class TheoryWhileStatement extends TheoryStatement {
	public final TheoryExpression	condition;
	public final TheoryLoopAnnotationsExpression loopAnnotations;
	public final TheoryBlockStatement	block;

	public TheoryWhileStatement(TheoryExpression condition,
			TheoryLoopAnnotationsExpression loopAnnotations,
			TheoryBlockStatement block) {
		this.condition = condition;
		this.loopAnnotations = loopAnnotations;
		this.block = block;
	}

	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
}
