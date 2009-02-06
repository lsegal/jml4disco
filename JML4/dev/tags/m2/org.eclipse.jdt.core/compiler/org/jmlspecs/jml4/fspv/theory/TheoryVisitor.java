/**
 * 
 */
package org.jmlspecs.jml4.fspv.theory;

/**
 * @author karabot
 *
 */
public class TheoryVisitor {

	///////////////////////////////////////////////////////////////////
	////////////////////////// Theory /////////////////////////////////
	///////////////////////////////////////////////////////////////////
	public Object accept(Theory theory) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryLemma lemma) {
		// TODO Auto-generated method stub
		return null;
	}

	///////////////////////////////////////////////////////////////////
	/////////////////////////// Types /////////////////////////////////
	///////////////////////////////////////////////////////////////////

	public Object accept(TheoryType theoryType) {
		// TODO Auto-generated method stub
		return null;
	}

	///////////////////////////////////////////////////////////////////
	//////////////////////// Variables ////////////////////////////////
	///////////////////////////////////////////////////////////////////

	public Object accept(TheoryVariable theoryVariable) {
		// TODO Auto-generated method stub
		return null;
	}
	
	///////////////////////////////////////////////////////////////////
	////////////////////// Statements /////////////////////////////////
	///////////////////////////////////////////////////////////////////

	public Object accept(TheoryAssignmentStatement theoryAssignmentStatement) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryConditionalStatement theoryConditionalStatement) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryWhileStatement theoryWhileStatement) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryBlockStatement theoryBlockStatement) {
		// TODO Auto-generated method stub
		return null;
	}
	
	public Object accept(TheoryLocalDeclarationBlockStatement theoryLocalDeclarationBlockStatement) {
		// TODO Auto-generated method stub		
		return null;
	}

	public Object accept(TheoryBindStatement theoryBindStatement) {
		// TODO Auto-generated method stub
		return null;
	}	

	public Object accept(TheoryStatement theoryStatement) {
		// TODO Auto-generated method stub
		return null;
	}

	///////////////////////////////////////////////////////////////////
	////////////////////// Expressions /////////////////////////////////
	///////////////////////////////////////////////////////////////////
	
	public Object accept(TheoryBinaryExpression theoryBinaryExpression) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryLiteral theoryLiteral) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryUnaryExpression theoryUnaryExpression) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryVariableReference theoryVariableReference) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryExpression theoryExpression) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryOperator theoryOperator) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryAssignmentExpression theoryAssignmentExpression) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryPostfixExpression theoryPostfixExpression) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryPrefixExpression theoryPrefixExpression) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryTempVariableReference theoryTempVariableReference) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryOldExpression theoryOldExpression) {
		// TODO Auto-generated method stub
		return null;
	}
	
	public Object accept(TheoryLoopAnnotationsExpression theoryLoopAnnotationsExpression) {
		// TODO Auto-generated method stub
		return null;		
	}

	public Object accept(TheoryVariantExpression theoryVariantExpression) {
		// TODO Auto-generated method stub
		return null;		
	}

	public Object accept(TheoryInvariantExpression theoryInvariantExpression) {
		// TODO Auto-generated method stub
		return null;		
	}

	public Object accept(TheoryQuantifiedExpression theoryQuantifiedExpression) {
		// TODO Auto-generated method stub
		return null;		
	}
	
}
