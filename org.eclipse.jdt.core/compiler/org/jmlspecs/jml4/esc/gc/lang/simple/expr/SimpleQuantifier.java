package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class SimpleQuantifier {
	public final TypeBinding type;
	public final String lexeme;

	public SimpleQuantifier(String lexeme, TypeBinding type) {
		this.lexeme = lexeme;
		this.type = type;
	}
	public String toString() {
		return this.lexeme;
	}

}
