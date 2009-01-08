package org.jmlspecs.jml4.ast;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

public class JmlStoreRefKeyword extends JmlStoreRef {

    public final static int NOTHING = 1;
    public final static int EVERYTHING = 2;
    public final static int NOT_SPECIFIED = 3;

	private final String keywordLexeme;
	public final int code;
	//@ invariant code == NOTHING || code == EVERYTHING || code == NOT_SPECIFIED;
	
	//@ ensures this.keywordLexeme = keywordLexeme;
	//@ ensures this.code = keywordLexeme2Code(keywordLexeme);
	public JmlStoreRefKeyword(String keywordLexeme) {
		super();
		this.keywordLexeme = keywordLexeme;
		this.code = keywordLexeme2Code(keywordLexeme);
	}
	
	public StringBuffer printExpression(int indent, StringBuffer output) {
		return output.append(this.keywordLexeme);
	}

	public void resolve(BlockScope scope) {
		/* empty, since there's nothing to resolve for this constant */
	}

	//@ requires lexeme.equals("\\nothing") || lexeme.equals("\\everything") || lexeme.equals("\\not_specified");
	//@ ensures  \result == NOTHING || \result == EVERYTHING || \result == NOT_SPECIFIED;
	private /*@ pure*/ static int keywordLexeme2Code(String lexeme) {
		switch (lexeme.charAt(4)) {
			case 'h' : return NOTHING; 
			case 'r' : return EVERYTHING; 
			case '_' : return NOT_SPECIFIED;
			default:
				Assert.isTrue(false, "Unexpected StoreRef Keyword: '"+lexeme+"'"); //$NON-NLS-1$ //$NON-NLS-2$
				return 0; // unreachable
		}
	}

	public FlowInfo analyseAssignment(BlockScope currentScope,
			FlowContext flowContext, FlowInfo flowInfo, Assignment assignment,
			boolean isCompound) {
		// TODO Auto-generated method stub
		return null;
	}

	public void generateAssignment(BlockScope currentScope,
			CodeStream codeStream, Assignment assignment, boolean valueRequired) {
		// TODO Auto-generated method stub
		
	}

	public void generateCompoundAssignment(BlockScope currentScope,
			CodeStream codeStream, Expression expression, int operator,
			int assignmentImplicitConversion, boolean valueRequired) {
		// TODO Auto-generated method stub
		
	}

	public void generatePostIncrement(BlockScope currentScope,
			CodeStream codeStream, CompoundAssignment postIncrement,
			boolean valueRequired) {
		// TODO Auto-generated method stub
		
	}
	
}
