package org.jmlspecs.jml4.ast;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public abstract class JmlQuantifier {
	/** The \forall quantifier lexeme. */
	public static final String FORALL = "\\forall"; //$NON-NLS-1$
	
	/** The \exists quantifier lexeme. */
	public static final String EXISTS = "\\exists"; //$NON-NLS-1$
	
	/** The \num_of quantifier lexeme. */
	public static final String NUM_OF = "\\num_of"; //$NON-NLS-1$

	/** The \max quantifier lexeme. */
	public static final String MAX = "\\max"; //$NON-NLS-1$
	
	/** The \min quantifier lexeme. */
	public static final String MIN = "\\min"; //$NON-NLS-1$
	
	/** The \product quantifier lexeme. */
	public static final String PRODUCT = "\\product"; //$NON-NLS-1$
	
	/** The \sum quantifier lexeme. */
	public static final String SUM = "\\sum"; //$NON-NLS-1$
	
	/** A map of all JML quantifiers, from quantifier lexeme (String) to JmlQuantifier object. */
	private static final Map QuantifierMap = new HashMap();
	
	/** The lexeme of this quantifier. */
	public final String lexeme;
	
	/** The type of this quantifier (null means the type of the body). */
	public final TypeBinding type; 
	
	/** The legal body types for this quantifier. */
	private final TypeBinding[] legalTypes;
	
	
	/** 
	 * Constructs a new JmlQuantifier with the specified properties. 
	 * 
	 * @param lexeme The lexeme.
	 * @param type The type.
	 * @param legalTypes The legal body types.
	 */
	//@ ensures this.lexeme == lexeme;
	//@ ensures this.type == type;
	//@ ensures this.legalTypes == legalTypes;	
	protected JmlQuantifier(/*@ non_null */ String lexeme, /*@ nullable */ TypeBinding type, 
			                /*@ non_null */ TypeBinding[] legalTypes) {
		this.lexeme = lexeme;
		this.type = type;
		this.legalTypes = legalTypes;
	}
	
	/**
	 * @return true if the specified type is legal for the body of this quantifier,
	 * false otherwise.
	 */
	public boolean isLegalType(/*@ non_null */ TypeBinding queryType) {
		for (int i = 0; i < legalTypes.length; i++) {
			if (queryType.isCompatibleWith(legalTypes[i])) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * @return the first legal type in the legal type array (for reporting purposes).
	 */
	public TypeBinding getFirstLegalType() {
		return legalTypes[0];
	}
	
	/**
	 * Generates code for this quantifier. Currently unimplemented, and likely to be implemented
	 * only in child classes. 
	 *
	 * @param boundVariables The bound variables.
	 * @param range The range.
	 * @param body The body.
	 * @param currentScope The current scope.
	 * @param codeStream The code stream.
	 * @param valueRequired The value required flag. 
	 */
	public abstract void generateCode(LocalDeclaration[] boundVariables, Expression range, Expression body, BlockScope currentScope, CodeStream codeStream, boolean valueRequired);
	
	// Static initializer, creates all the JML quantifier types
	
	static {
		// the JmlQuantifier objects put into the map are instances of child classes that will
		// eventually implement the code generation for the various quantifier types. 
		
		// \forall and \exists
		TypeBinding[] booleanOnly = new TypeBinding[] { TypeBinding.BOOLEAN };
		QuantifierMap.put(FORALL, new JmlBooleanQuantifier(FORALL, booleanOnly));
		QuantifierMap.put(EXISTS, new JmlBooleanQuantifier(EXISTS, booleanOnly));
		
		// \num_of
		QuantifierMap.put(NUM_OF, new JmlNumericQuantifier(NUM_OF, TypeBinding.LONG, booleanOnly));

		// \max, \min, \product and \sum
		TypeBinding[] builtInNumeric = 
			new TypeBinding[] { TypeBinding.DOUBLE, TypeBinding.BYTE, TypeBinding.CHAR, TypeBinding.SHORT,  
								TypeBinding.INT, TypeBinding.LONG, TypeBinding.FLOAT };
		QuantifierMap.put(MAX, new JmlNumericQuantifier(MAX, null, builtInNumeric));
		QuantifierMap.put(MIN, new JmlNumericQuantifier(MIN, null, builtInNumeric));
		QuantifierMap.put(PRODUCT, new JmlNumericQuantifier(PRODUCT, null, builtInNumeric));
		QuantifierMap.put(SUM, new JmlNumericQuantifier(SUM, null, builtInNumeric));
	}
	
	
	/**
	 * Factory method for obtaining quantifiers from quantifier lexemes.
	 * 
	 * @param lexeme The lexeme.
	 * @return the appropriate quantifier for the specified lexeme, or null if no 
	 * such quantifier exists.
	 */
	public static JmlQuantifier fromLexeme(/*@ non_null */ String lexeme)
	{
		return (JmlQuantifier) QuantifierMap.get(lexeme);
	}
}
