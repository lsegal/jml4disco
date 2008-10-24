package org.jmlspecs.jml4.esc.vc.lang;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class VcQuantifier {

	private static final String EXISTS_LEXEME  = "\\exists";  //$NON-NLS-1$
	private static final String FORALL_LEXEME  = "\\forall";  //$NON-NLS-1$
	private static final String SUM_LEXEME     = "\\sum";     //$NON-NLS-1$
	private static final String PRODUCT_LEXEME = "\\product"; //$NON-NLS-1$
	private static final String MIN_LEXEME     = "\\min";     //$NON-NLS-1$
	private static final String MAX_LEXEME     = "\\max";     //$NON-NLS-1$
	private static final String NUM_OF_LEXEME  = "\\num_of";  //$NON-NLS-1$

	public static final VcQuantifier FORALL = new VcQuantifier(FORALL_LEXEME, TypeBinding.BOOLEAN);

	public final TypeBinding type;
	public final String lexeme;

	public VcQuantifier(String lexeme, TypeBinding type) {
		this.lexeme = lexeme;
		this.type = type;
	}
	public String toString() {
		return this.lexeme;
	}

	public boolean isForall() {
		return this.lexeme == FORALL_LEXEME;
	}

	public boolean isExists() {
		return this.lexeme == EXISTS_LEXEME;
	}

	public boolean isSum() {
		return this.lexeme == SUM_LEXEME;
	}

	public boolean isProduct() {
		return this.lexeme == PRODUCT_LEXEME;
	}

	public boolean isMin() {
		return this.lexeme == MIN_LEXEME;
	}

	public boolean isMax() {
		return this.lexeme == MAX_LEXEME;
	}

	public boolean isNumOf() {
		return this.lexeme == NUM_OF_LEXEME;
	}

	public boolean isLogical() {
		return isForall() || isExists();
	}

	public boolean isNumeric() {
		return ! isLogical();
	}
}
