package org.jmlspecs.jml4.esc.gc.lang.simple.expr;



public class SimpleOperator {
	public static final SimpleOperator AND            = new SimpleOperator("&");  //$NON-NLS-1$
	public static final SimpleOperator OR             = new SimpleOperator("|");  //$NON-NLS-1$
	public static final SimpleOperator EQUALS         = new SimpleOperator("=="); //$NON-NLS-1$
	public static final SimpleOperator NOT_EQUALS     = new SimpleOperator("!="); //$NON-NLS-1$
	public static final SimpleOperator GREATER        = new SimpleOperator(">");  //$NON-NLS-1$
	public static final SimpleOperator GREATER_EQUALS = new SimpleOperator(">="); //$NON-NLS-1$
	public static final SimpleOperator LESS           = new SimpleOperator("<");  //$NON-NLS-1$
	public static final SimpleOperator LESS_EQUALS    = new SimpleOperator("<="); //$NON-NLS-1$
	
	public static final SimpleOperator PLUS      = new SimpleOperator("+"); //$NON-NLS-1$
	public static final SimpleOperator MINUS     = new SimpleOperator("-"); //$NON-NLS-1$
	public static final SimpleOperator TIMES     = new SimpleOperator("*"); //$NON-NLS-1$
	public static final SimpleOperator DIVIDE    = new SimpleOperator("/"); //$NON-NLS-1$
	public static final SimpleOperator REMAINDER = new SimpleOperator("%"); //$NON-NLS-1$

	public static final SimpleOperator IMPLIES     = new SimpleOperator("-->"); //$NON-NLS-1$
	public static final SimpleOperator REV_IMPLIES = new SimpleOperator("<--");   //$NON-NLS-1$
	public static final SimpleOperator EQUIV       = new SimpleOperator("<-->");  //$NON-NLS-1$
	public static final SimpleOperator NOT_EQUIV   = new SimpleOperator("<-!->"); //$NON-NLS-1$

	public final String name;
	private SimpleOperator(String name) {
		this.name = name;
	}
	public String toString() {
		return this.name;
	}
}
