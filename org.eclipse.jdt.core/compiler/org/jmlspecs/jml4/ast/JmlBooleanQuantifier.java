package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.impl.BooleanConstant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlBooleanQuantifier extends JmlQuantifier {
	/** 
	 * Constructs a new JmlQuantifier with the specified properties. 
	 * 
	 * @param lexeme The lexeme.
	 * @param legalTypes The legal body types.
	 */
	//@ ensures this.lexeme == lexeme;
	//@ ensures type == TypeBinding.BOOLEAN;
	//@ ensures (\forall int i; 0 <= i && i < legalTypes.length; isLegalType(legalTypes[i]));
	public JmlBooleanQuantifier(String lexeme, TypeBinding[] legalTypes) {
		super(lexeme, TypeBinding.BOOLEAN, legalTypes);
	}
	
	/**
	 * Generates code for this quantifier; currently, this just puts the constant value "true" on the stack.
	 * 
	 * @param boundVariables The bound variables.
	 * @param range The range.
	 * @param body The body.
	 * @param currentScope The current scope.
	 * @param codeStream The code stream.
	 * @param valueRequired The value required flag (unused here). 
	 */
	public void generateCode(LocalDeclaration[] boundVariables, Expression range, Expression body, BlockScope currentScope, CodeStream codeStream, boolean valueRequired) {
		if (valueRequired) {
			codeStream.generateConstant(BooleanConstant.fromValue(true), 0);
		}
	}
}
