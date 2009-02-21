package org.jmlspecs.jml4.fspv;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

import org.jmlspecs.jml4.fspv.theory.Theory;
import org.jmlspecs.jml4.fspv.theory.TheoryAssignmentExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryAssignmentStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryBinaryExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryBindStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryBlockStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryConditionalStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryHelper;
import org.jmlspecs.jml4.fspv.theory.TheoryLemma;
import org.jmlspecs.jml4.fspv.theory.TheoryLiteral;
import org.jmlspecs.jml4.fspv.theory.TheoryLocalDeclarationBlockStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryOperator;
import org.jmlspecs.jml4.fspv.theory.TheoryPostfixExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryPrefixExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryTempVariableReference;
import org.jmlspecs.jml4.fspv.theory.TheoryType;
import org.jmlspecs.jml4.fspv.theory.TheoryUnaryExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryVariable;
import org.jmlspecs.jml4.fspv.theory.TheoryVariableReference;
import org.jmlspecs.jml4.fspv.theory.TheoryVisitor;
import org.jmlspecs.jml4.fspv.theory.TheoryWhileStatement;

public class SideEffectHandler extends TheoryVisitor {
	
	private static final int INITIAL = -1;
	private HashMap incarnations;
	private TheoryHelper helper;

	public Object accept(Theory theory) {
		this.helper = new TheoryHelper();
		// Visit the lemmas in this theory
		TheoryLemma [] lemmas = new TheoryLemma[theory.lemmas.length];
		for(int i=0;i<theory.lemmas.length;i++)
			lemmas[i] = (TheoryLemma) theory.lemmas[i].visit(this);
		return new Theory(theory.name,lemmas);
	}

	public Object accept(TheoryLemma lemma) {
		// initialize the helper member
		this.helper.reset();
		this.incarnations = new HashMap();
		// Visit the variables.
		for(int i=0;i<lemma.variables.length;i++)
			lemma.variables[i].visit(this);
		// Visit the block of statements
		TheoryBlockStatement block = (TheoryBlockStatement) lemma.block.visit(this);
		return new TheoryLemma(lemma.variables, lemma.name, lemma.pre, block, lemma.post);
	}
	
	public Object accept(TheoryVariable theoryVariable) {
		// Populate the incarnations
		this.incarnations.put(theoryVariable,new Integer(INITIAL));
		return theoryVariable;
	}

	public Object accept(TheoryBlockStatement theoryBlockStatement) {
		// Add a new block stack

		this.helper.pushBlockStack();
		// Visit the statements
		for(int i=0;i<theoryBlockStatement.size();i++) {
			this.resetIncarnations();
			TheoryStatement s = (TheoryStatement) theoryBlockStatement.statementAt(i).visit(this);
			this.helper.push(s);
		}
		// Pop the new block
		TheoryBlockStatement result = this.helper.popStatements();
		return result;
	}

	public Object accept(TheoryLocalDeclarationBlockStatement theoryLocalDeclarationBlockStatement) {
		// Push a new local block stack
		this.helper.pushLocalVarStack(theoryLocalDeclarationBlockStatement.variable);
		// Visit the statements
		for(int i=0;i<theoryLocalDeclarationBlockStatement.size();i++) {
			this.resetIncarnations();
			TheoryStatement s = (TheoryStatement) theoryLocalDeclarationBlockStatement.statementAt(i).visit(this);
			this.helper.push(s);
		}
		TheoryBlockStatement result = this.helper.popStatements();
		return result;
	}

	///////////////////////////////////////////////////////////////////
	////////////////////// Statements /////////////////////////////////
	///////////////////////////////////////////////////////////////////
	
	public Object accept(TheoryAssignmentStatement theoryAssignmentStatement) {
		// decorate RHS expression if it contains side-effects?
		this.decorateExpressionForSideEffects(theoryAssignmentStatement.rhs);
		// Just visit the RHS.
		TheoryExpression rhs = (TheoryExpression) theoryAssignmentStatement.rhs.visit(this);
		TheoryAssignmentStatement result = new TheoryAssignmentStatement(theoryAssignmentStatement.lhs, rhs);
		return result;
	}

	public Object accept(TheoryConditionalStatement theoryConditionalStatement) {
		// Visit the condition and decorate all its nodes if it contains side-effects
		this.decorateExpressionForSideEffects(theoryConditionalStatement.condition);
		// Visit the condition and handle any side-effects
		TheoryExpression condition = (TheoryExpression) theoryConditionalStatement.condition.visit(this);
		// Visit the THEN block
		TheoryBlockStatement thenBlock = (TheoryBlockStatement) theoryConditionalStatement.thenBlock.visit(this);
		// Visit the ELSE block
		TheoryBlockStatement elseBlock = (TheoryBlockStatement) theoryConditionalStatement.elseBlock.visit(this);
		// Create the new conditional statement.
		TheoryConditionalStatement result = new TheoryConditionalStatement(condition,thenBlock,elseBlock);
		return result;
	}

	public Object accept(TheoryWhileStatement theoryWhileStatement) {
		// Visit the condition and decorate all its nodes if it contains side-effects
		this.decorateExpressionForSideEffects(theoryWhileStatement.condition);
		// Visit the condition and handle any side-effects
		TheoryExpression condition = (TheoryExpression) theoryWhileStatement.condition.visit(this);
		// Visit the block
		TheoryBlockStatement body = (TheoryBlockStatement) theoryWhileStatement.block.visit(this);
		// Create the new while statement.
		TheoryWhileStatement result = new TheoryWhileStatement(condition, theoryWhileStatement.loopAnnotations, body);
		return result;
	}

	///////////////////////////////////////////////////////////////////
	////////////////////// Expressions ////////////////////////////////
	///////////////////////////////////////////////////////////////////

	public Object accept(TheoryAssignmentExpression theoryAssignmentExpression) {
		TheoryVariableReference l = (TheoryVariableReference) theoryAssignmentExpression.assignment.lhs;
		TheoryExpression r = (TheoryExpression) theoryAssignmentExpression.assignment.rhs.visit(this);
		TheoryAssignmentStatement a = new TheoryAssignmentStatement(l, r);
		int i = this.incrementIncarnationFor(l.variable);
		TheoryTempVariableReference result = new TheoryTempVariableReference(l, i);
		TheoryBindStatement b = new TheoryBindStatement(result, a);
		this.helper.push(b);
		TheoryAssignmentStatement a1 = new TheoryAssignmentStatement(l,l);
		TheoryBindStatement b1 = new TheoryBindStatement(result,a1);
		this.helper.push(b1);		
		return result;
	}

	public Object accept(TheoryPostfixExpression theoryPostfixExpression) {
		TheoryVariableReference v = (TheoryVariableReference) theoryPostfixExpression.assignment.lhs;
		int i = this.incrementIncarnationFor(v.variable);
		TheoryTempVariableReference result = new TheoryTempVariableReference(v, i);
		TheoryBindStatement b = new TheoryBindStatement(result, theoryPostfixExpression.assignment);
		this.helper.push(b);
		return result;
	}

	public Object accept(TheoryPrefixExpression theoryPrefixExpression) {
		TheoryVariableReference v = (TheoryVariableReference) theoryPrefixExpression.assignment.lhs;		
		int i = this.incrementIncarnationFor(v.variable);
		TheoryTempVariableReference result = new TheoryTempVariableReference(v, i);
		TheoryBindStatement b = new TheoryBindStatement(result, theoryPrefixExpression.assignment);
		this.helper.push(b);
		TheoryAssignmentStatement a = new TheoryAssignmentStatement(v,v);
		TheoryBindStatement b1 = new TheoryBindStatement(result,a);
		this.helper.push(b1);
		return result;
	}

	public Object accept(TheoryBinaryExpression theoryBinaryExpression) {
		TheoryExpression l = (TheoryExpression) theoryBinaryExpression.lhs.visit(this);
		TheoryExpression r = (TheoryExpression) theoryBinaryExpression.rhs.visit(this);
		TheoryBinaryExpression result = new TheoryBinaryExpression(l,theoryBinaryExpression.op, r);
		return result;
	}

	public Object accept(TheoryLiteral theoryLiteral) {
		return theoryLiteral;
	}

	public Object accept(TheoryVariableReference theoryVariableReference) {
		TheoryVariable v = theoryVariableReference.variable;
		int i = ((Integer) this.incarnations.get(v)).intValue();
		TheoryVariableReference result = null;
		if(i == INITIAL) {
			if(theoryVariableReference.withSideEffects) {
				int idx = this.incrementIncarnationFor(theoryVariableReference.variable);
			  TheoryTempVariableReference vTemp = new TheoryTempVariableReference(theoryVariableReference, idx);
				TheoryAssignmentStatement a = new TheoryAssignmentStatement(theoryVariableReference, theoryVariableReference);
				TheoryBindStatement b = new TheoryBindStatement(vTemp, a);
				this.helper.push(b);
				result = vTemp;
			} else {
				result = theoryVariableReference;
			}
		}
		else
			result = new TheoryTempVariableReference(theoryVariableReference,i);
		return result;
	}

	public Object accept(TheoryUnaryExpression theoryUnaryExpression) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryExpression theoryExpression) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryStatement theoryStatement) {
		// TODO Auto-generated method stub
		return null;
	}

	public Object accept(TheoryOperator theoryOperator) {
		return theoryOperator;
	}

	public Object accept(TheoryType theoryType) {
		return theoryType;
	}

	
	///////////////////////////////////////////////////////////////////
	////////////////////////// Helpers ////////////////////////////////
	///////////////////////////////////////////////////////////////////

	private int incrementIncarnationFor(TheoryVariable variable) {
		Integer oi = (Integer) this.incarnations.get(variable);
		int result = oi.intValue() + 1;
		this.incarnations.put(variable, new Integer(result));
		return result;
	}

	private void resetIncarnations() {
		Set ks = this.incarnations.keySet();
		Iterator iter = ks.iterator();
		while(iter.hasNext()) {
			TheoryVariable v = (TheoryVariable) iter.next();
			this.incarnations.put(v, new Integer(INITIAL));
		}
		
	}

	private void decorateExpressionForSideEffects(TheoryExpression expression) {
		IsExpressionWithSideEffectVisitor seVisitor = new IsExpressionWithSideEffectVisitor();
		Boolean withSideEffect = (Boolean) expression.visit(seVisitor); 
		if(withSideEffect.booleanValue()) {
			DecorateExpressionWithSideEffectVisitor decVisitor = new DecorateExpressionWithSideEffectVisitor();
			expression.visit(decVisitor);
		}
	}
	
	// Determines if the expression is with side-effect - ONLY expressions should be passed to this visitor
	protected class IsExpressionWithSideEffectVisitor extends TheoryVisitor {

		public Object accept(TheoryBinaryExpression theoryBinaryExpression) {
			Boolean l = (Boolean) theoryBinaryExpression.lhs.visit(this);
			Boolean r = (Boolean) theoryBinaryExpression.rhs.visit(this);
			return new Boolean(l.booleanValue() || r.booleanValue());
		}

		public Object accept(TheoryLiteral theoryLiteral) {
			return new Boolean(false);
		}

		public Object accept(TheoryVariableReference theoryVariableReference) {
			return new Boolean(false);
		}

		public Object accept(TheoryAssignmentExpression theoryAssignmentExpression) {
			return new Boolean(true);
		}

		public Object accept(TheoryPostfixExpression theoryPostfixExpression) {
			return new Boolean(true);
		}

		public Object accept(TheoryPrefixExpression theoryPrefixExpression) {
			return new Boolean(true);
		}

	}

	// Decorates the expression nodes so that the expressions are tagge - ONLY expressions should be passed to this visitor
	protected class DecorateExpressionWithSideEffectVisitor extends TheoryVisitor {

		public Object accept(TheoryBinaryExpression theoryBinaryExpression) {
			theoryBinaryExpression.lhs.visit(this);
			theoryBinaryExpression.rhs.visit(this);
			theoryBinaryExpression.withSideEffects = true;
			return theoryBinaryExpression;
		}

		public Object accept(TheoryLiteral theoryLiteral) {
			theoryLiteral.withSideEffects = true;
			return theoryLiteral;
		}
		
		public Object accept(TheoryVariableReference theoryVariableReference) {
			theoryVariableReference.withSideEffects = true;
			return theoryVariableReference;
		}

		public Object accept(TheoryAssignmentExpression theoryAssignmentExpression) {
			theoryAssignmentExpression.withSideEffects = true;
			return theoryAssignmentExpression;
		}

		public Object accept(TheoryPostfixExpression theoryPostfixExpression) {
			theoryPostfixExpression.withSideEffects = true;
			return theoryPostfixExpression;
		}

		public Object accept(TheoryPrefixExpression theoryPrefixExpression) {
			theoryPrefixExpression.withSideEffects = true;
			return theoryPrefixExpression;
		}

	}

	
}
