package org.jmlspecs.jml4.esc.gc.lang.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class CfgQuantifier {

	public static final CfgQuantifier FORALL = new CfgQuantifier("\\forall", TypeBinding.BOOLEAN); //$NON-NLS-1$
	public final TypeBinding type;
	public final String lexeme;

	public CfgQuantifier(String lexeme, TypeBinding type) {
		this.lexeme = lexeme;
		this.type = type;
	}

	public String toString() {
		return this.lexeme;
	}

	public boolean equals(Object obj) {
		if (obj instanceof CfgQuantifier)
			return false;
		CfgQuantifier that = (CfgQuantifier) obj;
		return this.lexeme.equals(that.lexeme) && this.type.equals(that.type);
	}
}
