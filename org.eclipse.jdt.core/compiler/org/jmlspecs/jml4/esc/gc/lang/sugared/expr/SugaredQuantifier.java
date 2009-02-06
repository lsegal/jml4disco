package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class SugaredQuantifier {

	public final TypeBinding type;
	public final String lexeme;

	public SugaredQuantifier(String lexeme, TypeBinding type) {
		this.lexeme = lexeme;
		this.type = type;
	}
	public String toString() {
		return this.lexeme;
	}

}
