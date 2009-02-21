package org.jmlspecs.jml4.esc.vc.lang;



public class VcOperator {
	public static final VcOperator EQUALS         = new VcOperator("==", true); //$NON-NLS-1$
	public static final VcOperator NOT_EQUALS     = new VcOperator("!=", true); //$NON-NLS-1$
	public static final VcOperator GREATER        = new VcOperator(">",  true); //$NON-NLS-1$
	public static final VcOperator GREATER_EQUALS = new VcOperator(">=", true); //$NON-NLS-1$
	public static final VcOperator LESS           = new VcOperator("<",  true); //$NON-NLS-1$
	public static final VcOperator LESS_EQUALS    = new VcOperator("<=", true); //$NON-NLS-1$
	
	public static final VcOperator PLUS      = new VcOperator("+"); //$NON-NLS-1$
	public static final VcOperator MINUS     = new VcOperator("-"); //$NON-NLS-1$
	public static final VcOperator TIMES     = new VcOperator("*"); //$NON-NLS-1$
	public static final VcOperator DIVIDE    = new VcOperator("/"); //$NON-NLS-1$
	public static final VcOperator REMAINDER = new VcOperator("%"); //$NON-NLS-1$

	public static final VcOperator IMPLIES     = new VcOperator("-->");   //$NON-NLS-1$
	public static final VcOperator EQUIV       = new VcOperator("<-->");  //$NON-NLS-1$
	public static final VcOperator NOT_EQUIV   = new VcOperator("<-!->"); //$NON-NLS-1$

	public final String  name;
	public final boolean isEqualityOp;
	private VcOperator(String name, boolean isEqualityOp) {
		this.name = name;
		this.isEqualityOp = isEqualityOp;
	}
	private VcOperator(String name) {
		this(name, false);
	}
	public String toString() {
		return this.name;
	}
	public int hashCode() {
		return name.hashCode();
	}
}
