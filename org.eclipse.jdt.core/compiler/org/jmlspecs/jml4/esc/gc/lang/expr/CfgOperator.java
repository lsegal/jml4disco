package org.jmlspecs.jml4.esc.gc.lang.expr;



public class CfgOperator {
	public static final CfgOperator AND            = new CfgOperator("&");  //$NON-NLS-1$
	public static final CfgOperator OR             = new CfgOperator("|");  //$NON-NLS-1$
	public static final CfgOperator EQUALS         = new CfgOperator("=="); //$NON-NLS-1$
	public static final CfgOperator NOT_EQUALS     = new CfgOperator("!="); //$NON-NLS-1$
	public static final CfgOperator GREATER        = new CfgOperator(">");  //$NON-NLS-1$
	public static final CfgOperator GREATER_EQUALS = new CfgOperator(">="); //$NON-NLS-1$
	public static final CfgOperator LESS           = new CfgOperator("<");  //$NON-NLS-1$
	public static final CfgOperator LESS_EQUALS    = new CfgOperator("<="); //$NON-NLS-1$
	
	public static final CfgOperator PLUS      = new CfgOperator("+"); //$NON-NLS-1$
	public static final CfgOperator MINUS     = new CfgOperator("-"); //$NON-NLS-1$
	public static final CfgOperator TIMES     = new CfgOperator("*"); //$NON-NLS-1$
	public static final CfgOperator DIVIDE    = new CfgOperator("/"); //$NON-NLS-1$
	public static final CfgOperator REMAINDER = new CfgOperator("%"); //$NON-NLS-1$

	public static final CfgOperator IMPLIES     = new CfgOperator("-->");   //$NON-NLS-1$
	public static final CfgOperator REV_IMPLIES = new CfgOperator("<--");   //$NON-NLS-1$
	public static final CfgOperator EQUIV       = new CfgOperator("<-->");  //$NON-NLS-1$
	public static final CfgOperator NOT_EQUIV   = new CfgOperator("<-!->"); //$NON-NLS-1$

	public final String name;
	private CfgOperator(String name) {
		this.name = name;
	}
	public String toString() {
		return this.name;
	}
}
