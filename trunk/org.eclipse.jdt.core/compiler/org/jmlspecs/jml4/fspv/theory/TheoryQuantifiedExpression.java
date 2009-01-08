package org.jmlspecs.jml4.fspv.theory;

public class TheoryQuantifiedExpression extends TheoryExpression {

	public final TheoryQuantifier quantifier;
	public final TheoryVariable variable;
	public final TheoryExpression range;
	public final TheoryExpression body;

	public TheoryQuantifiedExpression(TheoryQuantifier quantifier, TheoryVariable variable, TheoryExpression range, TheoryExpression body) {
		super(body.type);
		this.quantifier = quantifier;
		this.variable = variable;
		this.range = range;
		this.body = body;
	}

	public String toString() {
		return "( " + this.quantifier + " " + this.variable + " ; " + this.range + " ; " + this.body + " )";  //$NON-NLS-1$ //$NON-NLS-2$//$NON-NLS-3$ //$NON-NLS-4$
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
