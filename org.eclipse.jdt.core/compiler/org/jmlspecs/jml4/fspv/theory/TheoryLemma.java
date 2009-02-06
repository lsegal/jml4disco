package org.jmlspecs.jml4.fspv.theory;

import org.jmlspecs.jml4.fspv.Fspv;


public class TheoryLemma {
	public static final String LEMMA_SUFFIX_SEPARATOR = "_"; //$NON-NLS-1$
	public final String name;
	public final TheoryVariable [] variables;
	public final TheoryExpression pre;
	public final TheoryBlockStatement block;
	public final TheoryExpression post;

	public TheoryLemma(TheoryVariable [] variables, String name, TheoryExpression pre, TheoryBlockStatement block, TheoryExpression post) {
		this.variables = variables;
		this.name = name;
		this.pre = pre;
		this.block = block;
		this.post = post;
	}
	
	public String toString() {
		String s = this.name;
		s += "\n" + Fspv.pretyPrintArray(this.variables); //$NON-NLS-1$
		s += "\n" + this.pre; //$NON-NLS-1$
		s += "\n" + this.block; //$NON-NLS-1$
		s += "\n" + this.post; //$NON-NLS-1$
		return s;
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}

}
