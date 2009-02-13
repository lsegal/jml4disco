package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;

/**
 * Instances of this class represent various JML keywords that are 
 * used in contexts where expressions (predicates or store references)
 * are expected.  It simplifies the overall AST definition to have
 * instances of this class be a subtype of Expression.
 *
 */
public class JmlKeywordExpression extends Expression {

	private final char[] keyword;
	
	private JmlKeywordExpression(char[] keyword) {
		this.keyword = keyword;
	}

	//=====================================================================
	// Class attributes:
	
	private final static char[] SLASH_EVERYTHING = "\\everything".toCharArray(); //$NON-NLS-1$
	private final static char[] SLASH_NOT_SPECIFIED = "\\not_specified".toCharArray(); //$NON-NLS-1$
	private final static char[] SLASH_NOTHING = "\\nothing".toCharArray(); //$NON-NLS-1$
	private final static char[] SLASH_SAME = "\\same".toCharArray(); //$NON-NLS-1$

	public final static JmlKeywordExpression NOTHING = new JmlKeywordExpression(SLASH_NOTHING);
	public final static JmlKeywordExpression EVERYTHING = new JmlKeywordExpression(SLASH_EVERYTHING);
	public final static JmlKeywordExpression NOT_SPECIFIED = new JmlKeywordExpression(SLASH_NOT_SPECIFIED);
	public final static JmlKeywordExpression SAME = new JmlKeywordExpression(SLASH_SAME);

//	public static JmlStoreRefKeyword getJmlStoreRefKeyword(char[] lexeme) {
//		switch (lexeme[4]) {
//		case 'h' : return NOTHING; 
//		case 'r' : return EVERYTHING; 
//		case '_' : return NOT_SPECIFIED;
//		default:
//			throw new IllegalArgumentException("Unrecognized StoreRef keyword: " + new String(lexeme)); //$NON-NLS-1$
//		}
//	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		return output.append(keyword);
	}

}
