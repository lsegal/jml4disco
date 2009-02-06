package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

public class SugaredOperator {

	public static final SugaredOperator AND            = new SugaredOperator("&");  //$NON-NLS-1$
	public static final SugaredOperator OR             = new SugaredOperator("|");  //$NON-NLS-1$
	public static final SugaredOperator EQUALS         = new SugaredOperator("=="); //$NON-NLS-1$
	public static final SugaredOperator NOT_EQUALS     = new SugaredOperator("!="); //$NON-NLS-1$
	public static final SugaredOperator GREATER        = new SugaredOperator(">");  //$NON-NLS-1$
	public static final SugaredOperator GREATER_EQUALS = new SugaredOperator(">="); //$NON-NLS-1$
	public static final SugaredOperator LESS           = new SugaredOperator("<");  //$NON-NLS-1$
	public static final SugaredOperator LESS_EQUALS    = new SugaredOperator("<="); //$NON-NLS-1$

	public static final SugaredOperator PLUS      = new SugaredOperator("+"); //$NON-NLS-1$
	public static final SugaredOperator MINUS     = new SugaredOperator("-"); //$NON-NLS-1$
	public static final SugaredOperator TIMES     = new SugaredOperator("*"); //$NON-NLS-1$
	public static final SugaredOperator DIVIDE    = new SugaredOperator("/"); //$NON-NLS-1$
	public static final SugaredOperator REMAINDER = new SugaredOperator("%"); //$NON-NLS-1$

	public static final SugaredOperator IMPLIES     = new SugaredOperator("-->");   //$NON-NLS-1$
	public static final SugaredOperator REV_IMPLIES = new SugaredOperator("<--");   //$NON-NLS-1$
	public static final SugaredOperator EQUIV       = new SugaredOperator("<-->");  //$NON-NLS-1$
	public static final SugaredOperator NOT_EQUIV   = new SugaredOperator("<-!->"); //$NON-NLS-1$

	public final String name;
	private SugaredOperator(String name) {
		this.name = name;
	}
	public String toString() {
		return this.name;
	}
}
