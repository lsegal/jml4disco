package org.jmlspecs.jml4.fspv;

import org.jmlspecs.jml4.fspv.theory.Theory;
import org.jmlspecs.jml4.fspv.theory.TheoryAssignmentStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryBinaryExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryBlockStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryConditionalStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryHelper;
import org.jmlspecs.jml4.fspv.theory.TheoryInvariantExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryLemma;
import org.jmlspecs.jml4.fspv.theory.TheoryLiteral;
import org.jmlspecs.jml4.fspv.theory.TheoryLocalDeclarationBlockStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryLoopAnnotationsExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryOldExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryQuantifiedExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryQuantifier;
import org.jmlspecs.jml4.fspv.theory.TheoryStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryVariable;
import org.jmlspecs.jml4.fspv.theory.TheoryVariableReference;
import org.jmlspecs.jml4.fspv.theory.TheoryVariantExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryVisitor;
import org.jmlspecs.jml4.fspv.theory.TheoryWhileStatement;

public class PrestateDecorator extends TheoryVisitor {

	private TheoryHelper helper;
	
	///////////////////////////////////////////////////////////////////
	////////////////////////// Theory /////////////////////////////////
	///////////////////////////////////////////////////////////////////
	
	public Object accept(Theory theory) {
		this.helper = new TheoryHelper();
		TheoryLemma [] lemmas = new TheoryLemma[theory.lemmas.length];
		for(int i = 0; i<lemmas.length; i++) {
			this.helper.reset();
			lemmas[i] = (TheoryLemma) theory.lemmas[i].visit(this);
		}
		return new Theory(theory.name,lemmas);
	}

	public Object accept(TheoryLemma lemma) {
		// visit the variables.  Additional assignments will be generated here and should be
		// added to the top of the body of statements.
		for(int i = 0; i<lemma.variables.length; i++)
			lemma.variables[i].visit(this);
		TheoryVariable [] vs = this.helper.getVariables();
		TheoryBlockStatement prestateAssignments = this.helper.popStatements();
		// visit the postcondition and update argument references to the one in the prestate.
		// Expressions inside \old will be dealt via the old visitor
		TheoryArgsToPrestateVisitor argsToPrestateVisitor = new TheoryArgsToPrestateVisitor();
		TheoryExpression post = (TheoryExpression) lemma.post.visit(argsToPrestateVisitor);
		// go over the post condition now and deal with \old expressions when they are found
		TheoryExpression post1 = (TheoryExpression) post.visit(this);
		// visit the body because we may have annotations that make use of \old()
		TheoryBlockStatement block = (TheoryBlockStatement) lemma.block.visit(this);
		// setup the new body.
		TheoryBlockStatement newBlock = TheoryBlockStatement.Merge(prestateAssignments,block);
		return new TheoryLemma(vs, lemma.name, lemma.pre, newBlock, post1);
	}

	///////////////////////////////////////////////////////////////////
	//////////////////////// Variables ////////////////////////////////
	///////////////////////////////////////////////////////////////////

	public Object accept(TheoryVariable theoryVariable) {
		this.helper.addVariable(theoryVariable);
		// We are dealing with an argument - i.e. we need pre-state info in case it is referred to in the postcondition
		if(theoryVariable.isArgument()) {
			// add the old variable for this argument
			TheoryVariable vOld = TheoryVariable.Old(theoryVariable);
			this.helper.addVariable(vOld);
			// add the assignments for the pre-state
			TheoryAssignmentStatement a = 
				new TheoryAssignmentStatement(vOld.nameReference(), theoryVariable.nameReference());
			this.helper.push(a);
		}
		// we throw away the return value so we can ignore this
		return theoryVariable;
	}

	///////////////////////////////////////////////////////////////////
	////////////////////// Statements /////////////////////////////////
	///////////////////////////////////////////////////////////////////
	public Object accept(TheoryAssignmentStatement theoryAssignmentStatement) {
		return theoryAssignmentStatement;
	}

	public Object accept(TheoryConditionalStatement theoryConditionalStatement) {
		TheoryBlockStatement thenBlock = (TheoryBlockStatement) theoryConditionalStatement.thenBlock.visit(this);
		TheoryBlockStatement elseBlock = (TheoryBlockStatement) theoryConditionalStatement.elseBlock.visit(this);		
		return new TheoryConditionalStatement(theoryConditionalStatement.condition, thenBlock, elseBlock);
	}

	public Object accept(TheoryWhileStatement theoryWhileStatement) {
		TheoryLoopAnnotationsExpression loopAnnotations = (TheoryLoopAnnotationsExpression) theoryWhileStatement.loopAnnotations.visit(this);
		TheoryBlockStatement block = (TheoryBlockStatement) theoryWhileStatement.block.visit(this);
		return new TheoryWhileStatement(theoryWhileStatement.condition,loopAnnotations,block);
	}

	public Object accept(TheoryBlockStatement theoryBlockStatement) {
		TheoryStatement [] ss = new TheoryStatement[theoryBlockStatement.size()];
		for(int i=0;i<ss.length;i++) {
			ss[i] = (TheoryStatement) theoryBlockStatement.statementAt(i).visit(this);
		}
		return new TheoryBlockStatement(ss);
	}
	
	public Object accept(TheoryLocalDeclarationBlockStatement theoryLocalDeclarationBlockStatement) {
		TheoryStatement [] ss = new TheoryStatement[theoryLocalDeclarationBlockStatement.size()];
		for(int i=0;i<ss.length;i++) {
			ss[i] = (TheoryStatement) theoryLocalDeclarationBlockStatement.statementAt(i).visit(this);
		}
		return new TheoryLocalDeclarationBlockStatement(theoryLocalDeclarationBlockStatement.variable,ss);
	}

	///////////////////////////////////////////////////////////////////
	////////////////////// Expressions ////////////////////////////////
	///////////////////////////////////////////////////////////////////

	public Object accept(TheoryLoopAnnotationsExpression theoryLoopAnnotationsExpression) {
		TheoryVariantExpression variant = (TheoryVariantExpression) theoryLoopAnnotationsExpression.variant.visit(this);
		TheoryInvariantExpression invariant =  (TheoryInvariantExpression) theoryLoopAnnotationsExpression.invariant.visit(this);
		return new TheoryLoopAnnotationsExpression(invariant,variant);
	}
	
	public Object accept(TheoryVariantExpression theoryVariantExpression) {
		TheoryExpression[] es = new TheoryExpression[theoryVariantExpression.size()];
		for(int i=0;i<es.length;i++) {
			es[i] = (TheoryExpression) theoryVariantExpression.expressionAt(i).visit(this);
		}
		return new TheoryVariantExpression(es);
	}
	
	public Object accept(TheoryInvariantExpression theoryInvariantExpression) {
		TheoryExpression[] es = new TheoryExpression[theoryInvariantExpression.size()];
		for(int i=0;i<es.length;i++) {
			es[i] = (TheoryExpression) theoryInvariantExpression.expressionAt(i).visit(this);
		}
		return new TheoryInvariantExpression(es);
	}
	
	public Object accept(TheoryBinaryExpression theoryBinaryExpression) {
		TheoryExpression l = (TheoryExpression) theoryBinaryExpression.lhs.visit(this);
		TheoryExpression r = (TheoryExpression) theoryBinaryExpression.rhs.visit(this);
		return new TheoryBinaryExpression(l, theoryBinaryExpression.op, r);
	}

	public Object accept(TheoryLiteral theoryLiteral) {
		return theoryLiteral;
	}

	public Object accept(TheoryVariableReference theoryVariableReference) {
		return theoryVariableReference;
	}

	public Object accept(TheoryOldExpression theoryOldExpression) {
		TheoryOldExpressionVisitor oldVisitor = new TheoryOldExpressionVisitor();
		return theoryOldExpression.visit(oldVisitor);
	}

	public Object accept(TheoryQuantifiedExpression theoryQuantifiedExpression) {
		TheoryExpression range = (TheoryExpression) theoryQuantifiedExpression.range.visit(this);
		TheoryExpression body =  (TheoryExpression) theoryQuantifiedExpression.body.visit(this);
		return new TheoryQuantifiedExpression(theoryQuantifiedExpression.quantifier, theoryQuantifiedExpression.variable, range, body);		
	}

	
	protected class TheoryOldExpressionVisitor extends TheoryVisitor {

		public Object accept(TheoryBinaryExpression theoryBinaryExpression) {
			TheoryExpression l = (TheoryExpression) theoryBinaryExpression.lhs.visit(this);
			TheoryExpression r = (TheoryExpression) theoryBinaryExpression.rhs.visit(this);
			return new TheoryBinaryExpression(l, theoryBinaryExpression.op, r);
		}

		public Object accept(TheoryLiteral theoryLiteral) {
			return theoryLiteral;
		}

		public Object accept(TheoryVariableReference theoryVariableReference) {
			if(theoryVariableReference.variable.isArgument()) {
				TheoryVariable vOld = TheoryVariable.Old(theoryVariableReference.variable);
				return new TheoryVariableReference(vOld);
			}
			return theoryVariableReference;
		}
		
		public Object accept(TheoryOldExpression theoryOldExpression) {
			// already inside an \old expression, just visit the expression
			return theoryOldExpression.expression.visit(this);
		}
		
		public Object accept(TheoryQuantifiedExpression theoryQuantifiedExpression) {
			TheoryExpression range = (TheoryExpression) theoryQuantifiedExpression.range.visit(this);
			TheoryExpression body =  (TheoryExpression) theoryQuantifiedExpression.body.visit(this);
			return new TheoryQuantifiedExpression(theoryQuantifiedExpression.quantifier, theoryQuantifiedExpression.variable, range, body);		
		}
		
	}

	protected class TheoryArgsToPrestateVisitor extends TheoryVisitor {

		public Object accept(TheoryOldExpression theoryOldExpression) {
			return theoryOldExpression; // deal with this elsewhere.
		}
		
		public Object accept(TheoryBinaryExpression theoryBinaryExpression) {
			TheoryExpression l = (TheoryExpression) theoryBinaryExpression.lhs.visit(this);
			TheoryExpression r = (TheoryExpression) theoryBinaryExpression.rhs.visit(this);
			return new TheoryBinaryExpression(l, theoryBinaryExpression.op, r);
		}

		public Object accept(TheoryLiteral theoryLiteral) {
			return theoryLiteral;
		}

		public Object accept(TheoryVariableReference theoryVariableReference) {
			if(theoryVariableReference.variable.isArgument()) {
				TheoryVariable vOld = TheoryVariable.Old(theoryVariableReference.variable);
				return new TheoryVariableReference(vOld);
			}
			return theoryVariableReference;
		}

		public Object accept(TheoryQuantifiedExpression theoryQuantifiedExpression) {
			TheoryExpression range = (TheoryExpression) theoryQuantifiedExpression.range.visit(this);
			TheoryExpression body =  (TheoryExpression) theoryQuantifiedExpression.body.visit(this);
			return new TheoryQuantifiedExpression(theoryQuantifiedExpression.quantifier, theoryQuantifiedExpression.variable, range, body);		
		}

	}


	
}
