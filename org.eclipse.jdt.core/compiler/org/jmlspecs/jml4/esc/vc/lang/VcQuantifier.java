package org.jmlspecs.jml4.esc.vc.lang;

import java.io.Serializable;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

//DISCO Serializable
public class VcQuantifier implements Serializable{

	private static final String EXISTS_LEXEME  = "\\exists";  //$NON-NLS-1$
	private static final String FORALL_LEXEME  = "\\forall";  //$NON-NLS-1$
	private static final String SUM_LEXEME     = "\\sum";     //$NON-NLS-1$
	private static final String PRODUCT_LEXEME = "\\product"; //$NON-NLS-1$
	private static final String MIN_LEXEME     = "\\min";     //$NON-NLS-1$
	private static final String MAX_LEXEME     = "\\max";     //$NON-NLS-1$
	private static final String NUM_OF_LEXEME  = "\\num_of";  //$NON-NLS-1$

	public static final VcQuantifier FORALL = new VcQuantifier(FORALL_LEXEME, TypeBinding.BOOLEAN);

	//DISCO transient for custom serialization
	transient public final TypeBinding type;
	public final String lexeme;

	public VcQuantifier(String lexeme, TypeBinding type) {
		this.lexeme = lexeme;
		this.type = type;
	}
	public String toString() {
		return this.lexeme;
	}

	//DISCO changed from == to .equals 
	public boolean isForall() {
		return this.lexeme.equals(FORALL_LEXEME);
	}

	public boolean isExists() {
		return this.lexeme.equals(EXISTS_LEXEME);
	}

	public boolean isSum() {
		return this.lexeme.equals(SUM_LEXEME);
	}

	public boolean isProduct() {
		return this.lexeme.equals(PRODUCT_LEXEME);
	}

	public boolean isMin() {
		return this.lexeme.equals(MIN_LEXEME);
	}

	public boolean isMax() {
		return this.lexeme.equals(MAX_LEXEME);
	}

	public boolean isNumOf() {
		return this.lexeme.equals(NUM_OF_LEXEME);
	}

	public boolean isLogical() {
		return isForall() || isExists();
	}

	public boolean isNumeric() {
		return ! isLogical();
	}
}
