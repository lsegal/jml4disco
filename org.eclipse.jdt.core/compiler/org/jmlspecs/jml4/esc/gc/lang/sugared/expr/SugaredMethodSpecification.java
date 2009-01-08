package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;


public class SugaredMethodSpecification {

	public static final SugaredMethodSpecification DEFAULT = new SugaredMethodSpecification(SugaredBooleanConstant.TRUE, SugaredBooleanConstant.TRUE, null);
	public final SugaredExpression pre;
	public final SugaredExpression post;
	private final /*@nullable*/ Object modifies;

	public SugaredMethodSpecification(SugaredExpression pre, SugaredExpression post, /*@nullable*/ Object modifies) {
		this.pre = pre;
		this.post = post;
		this.modifies = modifies;
	}

	public String toString() {
		return "[requires: "+this.pre+", modifies: "+this.modifies+", ensures: "+this.post+"]";   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$ //$NON-NLS-4$
	}

}
