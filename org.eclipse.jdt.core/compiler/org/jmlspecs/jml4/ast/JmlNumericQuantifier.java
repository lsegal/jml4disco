package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.impl.ByteConstant;
import org.eclipse.jdt.internal.compiler.impl.CharConstant;
import org.eclipse.jdt.internal.compiler.impl.DoubleConstant;
import org.eclipse.jdt.internal.compiler.impl.FloatConstant;
import org.eclipse.jdt.internal.compiler.impl.IntConstant;
import org.eclipse.jdt.internal.compiler.impl.LongConstant;
import org.eclipse.jdt.internal.compiler.impl.ShortConstant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeIds;

public class JmlNumericQuantifier extends JmlQuantifier {
	/** 
	 * Constructs a new JmlQuantifier with the specified properties. 
	 * 
	 * @param lexeme The lexeme.
	 * @param legalTypes The legal body types.
	 */
	//@ ensures this.lexeme == lexeme;
	//@ ensures this.type == type;
	//@ ensures (\forall int i; 0 <= i && i < legalTypes.length; isLegalType(legalTypes[i]));
	public JmlNumericQuantifier(String lexeme, /*@ nullable */ TypeBinding type, TypeBinding[] legalTypes) {
		super(lexeme, type, legalTypes);
	}
	
	/**
	 * Generates code for this quantifier; currently, this just puts the constant value 0 on the stack
	 * with an appropriate numeric type.
	 * 
	 * @param boundVariables The bound variables.
	 * @param range The range.
	 * @param body The body.
	 * @param currentScope The current scope.
	 * @param codeStream The code stream.
	 * @param valueRequired The value required flag (unused here). 
	 */
	public void generateCode(LocalDeclaration[] boundVariables, Expression range, Expression body, BlockScope currentScope, CodeStream codeStream, boolean valueRequired) {
		if (!valueRequired) {
			return;
		}
		
		// we need to generate a constant with our type or, if our type is null, 
		// the same type as the body; in any case, it's one of the seven numeric types.
		
		int typeId = body.resolvedType.id;
		if (type != null) {
			typeId = type.id;
		}
		
		switch (typeId) {
			case TypeIds.T_byte:
				codeStream.generateConstant(ByteConstant.fromValue((byte) 0), 0);
				break;
			case TypeIds.T_char:
				codeStream.generateConstant(CharConstant.fromValue((char) 0), 0);
				break;
			case TypeIds.T_short:
				codeStream.generateConstant(ShortConstant.fromValue((short) 0), 0);
				break;
			case TypeIds.T_int:
				codeStream.generateConstant(IntConstant.fromValue(0), 0);
				break;
			case TypeIds.T_long:
				codeStream.generateConstant(LongConstant.fromValue(0), 0);
				break;
			case TypeIds.T_float:
				codeStream.generateConstant(FloatConstant.fromValue(0), 0);
				break;
			case TypeIds.T_double:
				codeStream.generateConstant(DoubleConstant.fromValue(0), 0);
				break;
			default:
				// this should never happen
				currentScope.problemReporter().abortDueToInternalError("Invalid numeric quantifier type."); //$NON-NLS-1$
		}
	}
}
