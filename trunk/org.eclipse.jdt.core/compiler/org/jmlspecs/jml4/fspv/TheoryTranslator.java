package org.jmlspecs.jml4.fspv;

import java.util.Vector;

import org.eclipse.jdt.internal.compiler.ast.AND_AND_Expression;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.Block;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;
import org.eclipse.jdt.internal.compiler.ast.EqualExpression;
import org.eclipse.jdt.internal.compiler.ast.FalseLiteral;
import org.eclipse.jdt.internal.compiler.ast.IfStatement;
import org.eclipse.jdt.internal.compiler.ast.IntLiteral;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.OR_OR_Expression;
import org.eclipse.jdt.internal.compiler.ast.OperatorIds;
import org.eclipse.jdt.internal.compiler.ast.PostfixExpression;
import org.eclipse.jdt.internal.compiler.ast.PrefixExpression;
import org.eclipse.jdt.internal.compiler.ast.ReturnStatement;
import org.eclipse.jdt.internal.compiler.ast.SingleNameReference;
import org.eclipse.jdt.internal.compiler.ast.SingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.ast.UnaryExpression;
import org.eclipse.jdt.internal.compiler.ast.WhileStatement;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeIds;
import org.jmlspecs.jml4.ast.JmlAssignment;
import org.jmlspecs.jml4.ast.JmlClause;
import org.jmlspecs.jml4.ast.JmlCompilationUnitDeclaration;
import org.jmlspecs.jml4.ast.JmlLoopAnnotations;
import org.jmlspecs.jml4.ast.JmlLoopInvariant;
import org.jmlspecs.jml4.ast.JmlLoopVariant;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlOldExpression;
import org.jmlspecs.jml4.ast.JmlQuantifiedExpression;
import org.jmlspecs.jml4.ast.JmlQuantifier;
import org.jmlspecs.jml4.ast.JmlResultReference;
import org.jmlspecs.jml4.ast.JmlWhileStatement;
import org.jmlspecs.jml4.fspv.theory.Theory;
import org.jmlspecs.jml4.fspv.theory.TheoryAssignmentExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryAssignmentStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryBinaryExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryBlockStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryConditionalStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryHelper;
import org.jmlspecs.jml4.fspv.theory.TheoryInvariantExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryLemma;
import org.jmlspecs.jml4.fspv.theory.TheoryLiteral;
import org.jmlspecs.jml4.fspv.theory.TheoryLoopAnnotationsExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryOldExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryOperator;
import org.jmlspecs.jml4.fspv.theory.TheoryPostfixExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryPrefixExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryQuantifiedExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryQuantifier;
import org.jmlspecs.jml4.fspv.theory.TheoryStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryType;
import org.jmlspecs.jml4.fspv.theory.TheoryVariable;
import org.jmlspecs.jml4.fspv.theory.TheoryVariableReference;
import org.jmlspecs.jml4.fspv.theory.TheoryVariantExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryWhileStatement;
import org.jmlspecs.jml4.util.Logger;

public class TheoryTranslator extends TraceAstVisitor {
	private static final String LEMMA_NAME_SEPARATOR = "_"; //$NON-NLS-1$
	private static final String [] SUPPORTED_TYPES = {"int","boolean","void"}; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	public Theory theory;
	public TheoryHelper helper;

	private String className; 
	private String lemmaName; // <ClassName>_<MethodName>(_<param_type>)*
	private Vector addedInvariants;

	///////////////////////////////////////////////////////////////////
	//////////////// Compilation Unit - Top level node ////////////////
	///////////////////////////////////////////////////////////////////

	public boolean visit(JmlCompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		// Instantiate the theory helper
		this.helper = new TheoryHelper();
		return true;
	}
	public void endVisit(JmlCompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryLemma [] lemmas = this.helper.getLemmas();
		// Instantiate the theory object.
		this.theory = new Theory(new String(compilationUnitDeclaration.getMainTypeName()), lemmas);
	}

	public boolean visit(CompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}

	public void endVisit(CompilationUnitDeclaration compilationUnitDeclaration,	CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	///////////////////////////////////////////////////////////////////
	///////////////////////// Class Declarations //////////////////////
	///////////////////////////////////////////////////////////////////
	public boolean visit(TypeDeclaration typeDeclaration,	CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString() + " - " + new String(typeDeclaration.name)); //$NON-NLS-1$
		// Start setting up the lemma prefix.
		this.className = new String(typeDeclaration.name);
		return true;
	}
	public void endVisit(TypeDeclaration typeDeclaration,	CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	///////////////////////////////////////////////////////////////////
	/////////////////////////// Methods ///////////////////////////////
	///////////////////////////////////////////////////////////////////

	// JML Method node
	public boolean visit(JmlMethodDeclaration methodDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, new String(methodDeclaration.selector) + "\n" + this.toString()); //$NON-NLS-1$ 
		// add the method name to the lemma prefix
		this.lemmaName = this.className + LEMMA_NAME_SEPARATOR + new String(methodDeclaration.selector);
		this.helper.reset();
		this.addedInvariants = new Vector();
		// Add the result variable if there is a return value
		// We do it at the start of the method traversal because possible references to it will be able
		// find the VariableReference in the helper object.
		if (methodDeclaration.returnType != null && methodDeclaration.binding.returnType.id != TypeIds.T_void) {
			TheoryType type = jdtType2TheoryType(methodDeclaration.binding.returnType);
			this.helper.addVariable(TheoryVariable.Result(type));
		}
		return true;
	}
	public void endVisit(JmlMethodDeclaration methodDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		// Translate the precondition postcondition
		// FIXME: maybe we should add traverse() methods to all specification related AST nodes.
		// FIXME: if traverse methods are added it will break this algorithm.
		TheoryExpression pre = TheoryLiteral.True();
		TheoryExpression post= TheoryLiteral.True();
		if(methodDeclaration.specification != null) {
			// traverse through the precondition expression
			methodDeclaration.specification.getPrecondition().traverse(this, methodDeclaration.scope);
			pre =  this.helper.popExpression();
			// traverse through the postcondition expression
			methodDeclaration.specification.getPostcondition().traverse(this, methodDeclaration.scope);
			post = this.helper.popExpression();
		}
		// Get the theory variables
		TheoryVariable [] vs = this.helper.getVariables();
		// Deal with the local variable blocks
		while(this.helper.isLocalVarStack()) {
			TheoryBlockStatement localVarBlock = this.helper.popStatements();
			this.helper.push(localVarBlock);
		}
		// At this point we should have a TheoryStack of type TOP - fail if this is not the case!
		if(! this.helper.isTopStack()) 
			throw new RuntimeException("Stack of type TOP not found!");  //$NON-NLS-1$
		// Get the main body of statements.
		TheoryBlockStatement block = this.helper.popStatements();
		// Create the lemma
		TheoryLemma lemma = new TheoryLemma(vs, this.lemmaName, pre, block, post);
		this.helper.addLemma(lemma);
	}

	// JDT Method node - do nothing, all processing is done at the JML level
	// This stabs are still needed because we need to return true.  This will
	// trigger traversal of the fields of MethodDeclaration.
	public boolean visit(MethodDeclaration methodDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(MethodDeclaration methodDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Argument - method parameters, etc
	// TODO: Is method declarations the only place arguments nodes are used?
	public boolean visit(Argument argument, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(Argument argument, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		// Add argument to the list of variables available to this lemma
		TheoryType type = this.jdtType2TheoryType(argument.binding.type);
		TheoryVariable v = TheoryVariable.Argument(new String(argument.name), type, argument.sourceStart());
		this.helper.addVariable(v);
		// Add loop invariant clauses for each argument so that its relationship with the 
		// prestate is maintained when a while statement is encountered.  This is a temporary fix
		// and it only works with arguments. FIXME
		TheoryVariableReference vr = v.nameReference();
		TheoryBinaryExpression be = new TheoryBinaryExpression(vr,TheoryOperator.Equal(), new TheoryOldExpression(vr));
		this.addedInvariants.add(be);
		// add the types of the arguments to the lemma name.
		this.lemmaName += TheoryLemma.LEMMA_SUFFIX_SEPARATOR + type;
	}

	///////////////////////////////////////////////////////////////////
	/////////////////////////// Types /////////////////////////////////
	///////////////////////////////////////////////////////////////////

	//// Single type references - anything other than the supported types will throw an exception.
	public boolean visit(SingleTypeReference singleTypeReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		// Test that the type is supported
		if(! this.isTypeSupported(singleTypeReference.toString()))
			throw new NoSupportException(singleTypeReference.toString());
		return true;
	}
	public void endVisit(SingleTypeReference singleTypeReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	///////////////////////////////////////////////////////////////////
	////////////////////// Statements /////////////////////////////////
	///////////////////////////////////////////////////////////////////

	// local variable declarations
	public boolean visit(LocalDeclaration localDeclaration, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(LocalDeclaration localDeclaration, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression e = null;
		if(localDeclaration.initialization != null) {
			e = this.helper.popExpression();
		}
		TheoryType type = this.jdtType2TheoryType(localDeclaration.binding.type);
		TheoryVariable v = TheoryVariable.Local(new String(localDeclaration.name), type, null, localDeclaration.sourceStart());
		// add the local variable into the hoarestate - even though this is a local variable it is still
		// required to be in the hoarestate - this requirement is made by Simpl.  I found out the hard way.
		this.helper.addVariable(v);
//		this.helper.pushLocalVarStack(v); // Enabling/Disabling this statement turns on/off local variable support.
		// Create an assignment statement that will perform the variable initialization
		// This is done because it will make handling of side-effects in initialization expressions
		// simpler.
		if(e != null) {
			TheoryAssignmentStatement a = new TheoryAssignmentStatement(new TheoryVariableReference(v),e);
			this.helper.push(a);
		}
	}

	// return
	public boolean visit(ReturnStatement returnStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(ReturnStatement returnStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		if (returnStatement.expression != null) {
			TheoryVariable v = new TheoryVariable(TheoryVariable.RESULT_NAME, null, null, TheoryVariable.RESULT, 0);
			TheoryVariable vFromHelper = this.helper.lookupVariable(v);
			TheoryVariableReference l = new TheoryVariableReference(vFromHelper);
			TheoryExpression r = this.helper.popExpression();
			TheoryAssignmentStatement s = new TheoryAssignmentStatement(l, r);
			this.helper.push(s);
		}
	}

	// Block - { ... }
	public boolean visit(Block block, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		this.helper.pushBlockStack();
		return true;
	}
	public void endVisit(Block block, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		// Deal with the local variable blocks
		while(this.helper.isLocalVarStack()) {
			TheoryBlockStatement localVarBlock = this.helper.popStatements();
			this.helper.push(localVarBlock);
		}
		// Now get the statements for this block
		TheoryBlockStatement theoryBlock = this.helper.popStatements();
		this.helper.push(theoryBlock);
	}	

	///////////////////////////////////////////////////////////////////
	/////////////////////// IF THEN ELSE //////////////////////////////
	///////////////////////////////////////////////////////////////////
	public boolean visit(IfStatement ifStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(IfStatement ifStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		// Deal with ELSE part
		TheoryBlockStatement elseBlock = TheoryBlockStatement.EMPTY_BLOCK;
		if(ifStatement.elseStatement != null) {
			TheoryStatement statement = this.helper.popStatement();
			if(statement instanceof TheoryBlockStatement)
				elseBlock = (TheoryBlockStatement) statement;
			else
				elseBlock = new TheoryBlockStatement(new TheoryStatement[] {statement});
		}
		// Deal with THEN part
		TheoryBlockStatement thenBlock = TheoryBlockStatement.EMPTY_BLOCK;
		if(ifStatement.thenStatement != null) {
			TheoryStatement statement = this.helper.popStatement();
			if(statement instanceof TheoryBlockStatement)
				thenBlock = (TheoryBlockStatement) statement;
			else
				thenBlock = new TheoryBlockStatement(new TheoryStatement[] {statement});
		}
		// Post the condition
		TheoryExpression condition = this.helper.popExpression();
		// Create the new TheoryConditionalStatement
		TheoryConditionalStatement s = new TheoryConditionalStatement(condition, thenBlock, elseBlock);
		// Push the statement to the stack
		this.helper.push(s);
	}

	///////////////////////////////////////////////////////////////////
	/////////////////////////// LOOPS /////////////////////////////////
	///////////////////////////////////////////////////////////////////

	// while
	// Unlike all other methods we handle while statements in the visit part of
	// of the visitor.  It is simply to confusing to do otherwise.
	public boolean visit(JmlWhileStatement whileStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		// Handle the condition
		whileStatement.condition.traverse(this, scope);
		TheoryExpression condition = this.helper.popExpression();
		// Handle variants/invariants
		TheoryLoopAnnotationsExpression loopAnnotations = TheoryLoopAnnotationsExpression.EMPTY_LOOP_ANNOTATIONS;
		if(whileStatement.annotations != null) {
			whileStatement.annotations.traverse(this, scope);
			loopAnnotations = (TheoryLoopAnnotationsExpression) this.helper.popExpression();
		}
		// Handle the loop body
		TheoryBlockStatement block = TheoryBlockStatement.EMPTY_BLOCK;
		if (whileStatement.action != null) {
			whileStatement.action.traverse(this, scope);
			TheoryStatement statement = this.helper.popStatement();
			if(statement instanceof TheoryBlockStatement)
				block = (TheoryBlockStatement) statement;
			else
				block = new TheoryBlockStatement(new TheoryStatement[] {statement});
		}
		// Create the while statement
		TheoryWhileStatement w = new TheoryWhileStatement(condition, loopAnnotations, block);
		this.helper.push(w);
		return false;
	}
	public void endVisit(JmlWhileStatement whileStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	// I still need to take care of this because nodes with no annotations
	// will be WhileStatement and not JmlWhileStatement.
	// TODO: Consider changing this so that we are always with a JmlWhileStatement
	//       node irrespective to annotations.
	public boolean visit(WhileStatement whileStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); 
		JmlWhileStatement w = new JmlWhileStatement(null,whileStatement.condition,whileStatement.action,whileStatement.sourceStart(),whileStatement.sourceEnd());
		w.traverse(this, scope);
		return false;
	}


	///////////////////////////////////////////////////////////////////
	////////////////////// Expressions /////////////////////////////////
	///////////////////////////////////////////////////////////////////

	// Postfix expressions - i.e. x++ x--, etc.
	public boolean visit(PostfixExpression postfixExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());return true;
	}
	public void endVisit(PostfixExpression postfixExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression l = this.helper.popExpression();
		postfixExpression.expression.traverse(this, scope);
		TheoryExpression r = this.helper.popExpression();
		BinaryExpression be = new BinaryExpression(postfixExpression.lhs,postfixExpression.expression,postfixExpression.operator);
		TheoryOperator op = this.jdtOp2TheoryOp(be);
		TheoryBinaryExpression newr = new TheoryBinaryExpression(l, op, r);
		TheoryAssignmentStatement a = new TheoryAssignmentStatement(l,newr);
		if(postfixExpression.statementEnd != -1) { // Statement
			this.helper.push(a);	
		} else { // Expression
			TheoryPostfixExpression e = new TheoryPostfixExpression(a);
			this.helper.push(e);
		}
	}

	// Prefix expressions - i.e. ++x, --x, etc.
	public boolean visit(PrefixExpression prefixExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());return true;		 
	}	 
	public void endVisit(PrefixExpression prefixExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression l = this.helper.popExpression();
		prefixExpression.expression.traverse(this, scope);
		TheoryExpression r = this.helper.popExpression();
		BinaryExpression be = new BinaryExpression(prefixExpression.lhs,prefixExpression.expression,prefixExpression.operator);
		TheoryOperator op = this.jdtOp2TheoryOp(be);
		TheoryBinaryExpression newr = new TheoryBinaryExpression(l, op, r);
		TheoryAssignmentStatement a = new TheoryAssignmentStatement(l,newr);
		if(prefixExpression.statementEnd != -1) { // Statement
			this.helper.push(a);			
		} else { // Expression
			TheoryPrefixExpression e = new TheoryPrefixExpression(a);
			this.helper.push(e);			
		}
	}

	// Jml Assignment
	public boolean visit(JmlAssignment assignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());return true;
	}
	public void endVisit(JmlAssignment assignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression r = this.helper.popExpression();
		TheoryExpression l = this.helper.popExpression();
		TheoryAssignmentStatement a = new TheoryAssignmentStatement(l,r);
		if(assignment.statementEnd != -1) { // Statement
			this.helper.push(a);			
		} else { // Expression
			TheoryAssignmentExpression e = new TheoryAssignmentExpression(a);
			this.helper.push(e);			
		}
	}
	// JDT Assignment - this is needed so that we let the traversal to
	// continue to the childen nodes of the assignment.
	public boolean visit(Assignment assignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(Assignment assignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Compound Assignment - +=. -=, *=, /=
	public boolean visit(CompoundAssignment compoundAssignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(CompoundAssignment compoundAssignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression r = this.helper.popExpression();
		TheoryExpression l = this.helper.popExpression();
		BinaryExpression be = new BinaryExpression(compoundAssignment.lhs,compoundAssignment.expression,compoundAssignment.operator);
		TheoryOperator op = this.jdtOp2TheoryOp(be);
		TheoryBinaryExpression newr = new TheoryBinaryExpression(l, op, r);
		TheoryAssignmentStatement a = new TheoryAssignmentStatement(l,newr);
		if(compoundAssignment.statementEnd != -1) { // Statement
			this.helper.push(a);			
		} else { // Expression
			TheoryAssignmentExpression e = new TheoryAssignmentExpression(a);
			this.helper.push(e);			
		}
	}

	// Equality - ==, !=, etc.
	public boolean visit(EqualExpression equalExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(EqualExpression equalExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression r = this.helper.popExpression();
		TheoryExpression l = this.helper.popExpression();
		TheoryOperator op = jdtOp2TheoryOp(equalExpression);
		TheoryBinaryExpression be = new TheoryBinaryExpression(l,op,r);
		this.helper.push(be);
	}

	// AND_AND expressions
	public boolean visit(AND_AND_Expression and_and_Expression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(AND_AND_Expression and_and_Expression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression r = this.helper.popExpression();
		TheoryExpression l = this.helper.popExpression();
		TheoryOperator op = this.jdtOp2TheoryOp(and_and_Expression);
		TheoryBinaryExpression be = new TheoryBinaryExpression(l, op, r);
		this.helper.push(be);
	}

	// OR_OR expressions
	public boolean visit(OR_OR_Expression or_or_Expression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(OR_OR_Expression or_or_Expression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression r = this.helper.popExpression();
		TheoryExpression l = this.helper.popExpression();
		TheoryOperator op = this.jdtOp2TheoryOp(or_or_Expression);
		TheoryBinaryExpression be = new TheoryBinaryExpression(l, op, r);
		this.helper.push(be);
	}

	//Binary 
	public boolean visit(BinaryExpression binaryExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(BinaryExpression binaryExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression r = this.helper.popExpression();
		TheoryExpression l = this.helper.popExpression();
		TheoryOperator op = jdtOp2TheoryOp(binaryExpression);
		TheoryBinaryExpression be = new TheoryBinaryExpression(l,op,r);
		this.helper.push(be);
	}

	// TODO: Variable references
	public boolean visit(SingleNameReference singleNameReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(SingleNameReference singleNameReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		if(singleNameReference.binding.kind() == Binding.LOCAL) {
			LocalVariableBinding binding = (LocalVariableBinding)singleNameReference.binding;			
			String name = new String(singleNameReference.token);
			TheoryVariable vTmp = new TheoryVariable(name, null, null, -1, binding.declaration.sourceStart());
			TheoryVariable vFromHelper = this.helper.lookupVariable(vTmp);
			TheoryVariableReference v = new TheoryVariableReference(vFromHelper);
			this.helper.push(v);
		}
		else
			throw new NoSupportException("Variable type of this reference is not supported [" + singleNameReference + "]");  //$NON-NLS-1$//$NON-NLS-2$
	}

	// TODO: Side-effects

	// Literals

	//// Integers
	public boolean visit(IntLiteral intLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryLiteral l = new TheoryLiteral(intLiteral.toString(), TheoryType.Int());
		this.helper.push(l);
		return true;
	}
	public void endVisit(IntLiteral intLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	//// Boolean False 
	public boolean visit(FalseLiteral falseLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryLiteral l = TheoryLiteral.False();
		this.helper.push(l);
		return true;
	}
	public void endVisit(FalseLiteral falseLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	//// Boolean True
	public boolean visit(TrueLiteral trueLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryLiteral l = TheoryLiteral.True();
		this.helper.push(l);		
		return true;
	}
	public void endVisit(TrueLiteral trueLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	///////////////////////////////////////////////////////////////////
	///////////////////////////// JML /////////////////////////////////
	///////////////////////////////////////////////////////////////////

	 public boolean visit(JmlQuantifiedExpression expr, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
		 // Translate the quantified operator
		 TheoryQuantifier quantifier = this.jmlQuant2Theory(expr.quantifier);
		 // Add the local declarations to the list of variables
		 LocalDeclaration l = expr.boundVariables[0];
		 TheoryType type = this.jdtType2TheoryType(l.binding.type);
		 TheoryVariable v = TheoryVariable.Bound(new String(l.name), type, null, l.sourceStart());
		 this.helper.addVariable(v);
		 // Translate the range expression
		 expr.range.traverse(this, scope);
		 TheoryExpression range = this.helper.popExpression();
		 // Translate the body
		 expr.body.traverse(this, scope);
		 TheoryExpression body = this.helper.popExpression();
		 // Create the quantifier expression
		 TheoryQuantifiedExpression qe = new TheoryQuantifiedExpression(quantifier, v, range, body);
		 // push it for the parent to pick up
		 this.helper.push(qe);
		 // stop traversing here
		 return false;
	 }
	public void endVisit(JmlQuantifiedExpression expr, BlockScope scope) {
		 Logger.printlnWithTrace(0, this.toString());
	 }
	
	// \old
	public boolean visit(UnaryExpression unaryExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(UnaryExpression unaryExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		if (unaryExpression instanceof JmlOldExpression) {
			TheoryExpression e = this.helper.popExpression();
			TheoryOldExpression oe = new TheoryOldExpression(e);
			this.helper.push(oe);
		} else {
			throw new NoSupportException(unaryExpression.toString());
		}
	}
	
	// \result
	public boolean visit(JmlResultReference resultReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(JmlResultReference resultReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryVariable vTmp = new TheoryVariable(TheoryVariable.RESULT_NAME, null, null, TheoryVariable.LOCAL, 0);
		TheoryVariable vFromHelper = this.helper.lookupVariable(vTmp);
		TheoryVariableReference v = new TheoryVariableReference(vFromHelper);
		this.helper.push(v);
	}

	// Loop Annotations
	// Again we do the work in the visit part because it gets to complicated to
	// do it in the endVisit.
	public boolean visit(JmlLoopAnnotations jmlLoopAnnotations, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); 
		// BinaryExpression that hold the implicit invariant introduced because of the variant
		TheoryBinaryExpression be = null;
		// Handle loop variants
		TheoryVariantExpression variant = TheoryVariantExpression.EMPTY_VARIANT;
		if(jmlLoopAnnotations.variants != null) {
			TheoryExpression[] es = new TheoryExpression[jmlLoopAnnotations.variants.length];
			for(int i=0; i<es.length;i++) {
				jmlLoopAnnotations.variants[i].traverse(this, scope);
				TheoryExpression e = this.helper.popExpression();
				be = new TheoryBinaryExpression(e,TheoryOperator.GreaterEqual(), TheoryLiteral.Zero(e.type));
				es[i] = e;
			}
			variant = new TheoryVariantExpression(es);
		}
		// Handle loop invariants
		TheoryInvariantExpression invariant = TheoryInvariantExpression.EMPTY_INVARIANT;
		if(jmlLoopAnnotations.invariants != null) {
			int size = jmlLoopAnnotations.invariants.length;
			// Add space for the implicit invariant because of the variant
			if(be != null) size++;
			// Add space for the invariants to work around the problem of havocing everything, as simpl is doing.
			if(this.addedInvariants.size()>0)
				size+=this.addedInvariants.size();
			// Allocate the space in the invariants array.
			TheoryExpression[] es = new TheoryExpression[size];
			// add the implicit invariant because of the variant
			int currentIdx = jmlLoopAnnotations.invariants.length;
			if(be != null) {
				es[currentIdx] = be;
				currentIdx++;
			}
			// add the added invariants because of havocing.
			for(int i=0;i<this.addedInvariants.size(); i++) {
				es[currentIdx+i]=(TheoryExpression) this.addedInvariants.elementAt(i);
			}
			for(int i=0; i<jmlLoopAnnotations.invariants.length;i++) {
				jmlLoopAnnotations.invariants[i].traverse(this, scope);
				es[i] = this.helper.popExpression();
			}
			invariant = new TheoryInvariantExpression(es);			 
		}
		// Create the loop annotations.
		TheoryLoopAnnotationsExpression la = new TheoryLoopAnnotationsExpression(invariant,variant);
		this.helper.push(la);
		return false;
	}
	public void endVisit(JmlLoopAnnotations jmlLoopAnnotations, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Loop Invariants
	public boolean visit(JmlLoopInvariant jmlLoopInvariant, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(JmlLoopInvariant jmlLoopInvariant, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Loop Variants
	public boolean visit(JmlLoopVariant jmlLoopVariant, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(JmlLoopVariant jmlLoopVariant, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Jml Clause - needed to be true for at least invariants
	// TODO: What else is this used for?
	public boolean visit(JmlClause jmlClause, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());return true;
	}
	public void endVisit(JmlClause jmlClause, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}


	///////////////////////////////////////////////////////////////////
	////////////////////// Helper methods /////////////////////////////
	///////////////////////////////////////////////////////////////////

	 private TheoryQuantifier jmlQuant2Theory(JmlQuantifier quantifier) {
		 if(quantifier.lexeme.equals(JmlQuantifier.EXISTS))
			 return TheoryQuantifier.exists();
		 else if(quantifier.lexeme.equals(JmlQuantifier.FORALL))
			 return TheoryQuantifier.forall();
//		 else if(quantifier.lexeme.equals(JmlQuantifier.MAX))
//			 return TheoryQuantifier.max();
//		 else if(quantifier.lexeme.equals(JmlQuantifier.MIN))
//			 return TheoryQuantifier.min();
		 else if(quantifier.lexeme.equals(JmlQuantifier.NUM_OF))
			 return TheoryQuantifier.numOf();
		 else if(quantifier.lexeme.equals(JmlQuantifier.SUM))
			 return TheoryQuantifier.sum();
		 else if(quantifier.lexeme.equals(JmlQuantifier.PRODUCT))
			 return TheoryQuantifier.product();
		 // croak if we have not found a match yet
		 throw new NoSupportException(quantifier.toString());		 
	}
	
	private boolean isTypeSupported(String type) {
		for(int i = 0; i<SUPPORTED_TYPES.length; i++)
			if(type.equals(SUPPORTED_TYPES[i]))
				return true;
		return false;
	}

	private TheoryOperator jdtOp2TheoryOp(BinaryExpression e) {
		int op = (e.bits & ASTNode.OperatorMASK) >> ASTNode.OperatorSHIFT; 
		switch (op) {
		case OperatorIds.EQUAL_EQUAL : // "=="
			return TheoryOperator.Equal();
		case OperatorIds.LESS_EQUAL : // "<="
			return TheoryOperator.LessEqual();
		case OperatorIds.GREATER_EQUAL : // ">="
			return TheoryOperator.GreaterEqual();
		case OperatorIds.NOT_EQUAL : // "!="
			return TheoryOperator.NotEqual();
		case OperatorIds.OR_OR : // "||"
			return TheoryOperator.OrOr();
		case OperatorIds.AND_AND : // "&&"
			return TheoryOperator.AndAnd();
		case OperatorIds.PLUS : // "+"
			return TheoryOperator.Plus();
		case OperatorIds.MINUS : // "-"
			return TheoryOperator.Minus();
		case OperatorIds.NOT : // "!"
			return TheoryOperator.Not();
		case OperatorIds.REMAINDER : // "%"
			return TheoryOperator.Remainder();
		case OperatorIds.AND : //"&"
			return TheoryOperator.And();
		case OperatorIds.MULTIPLY :  //"*"
			return TheoryOperator.Multiply();
		case OperatorIds.OR : // "|"
			return TheoryOperator.Or();
		case OperatorIds.DIVIDE : // "/"
			return TheoryOperator.Divide();
		case OperatorIds.GREATER :  // ">"
			return TheoryOperator.Greater();
		case OperatorIds.LESS : //"<"
			return TheoryOperator.Less();

		case OperatorIds.QUESTIONCOLON : //"?:"
			//			return TheoryOperator.QuestionColon();
		case OperatorIds.LEFT_SHIFT : //"<<"
		case OperatorIds.RIGHT_SHIFT : //">>"
		case OperatorIds.UNSIGNED_RIGHT_SHIFT : // ">>>"
		case OperatorIds.XOR : // "^"
		case OperatorIds.TWIDDLE : // "~"
		case OperatorIds.EQUAL : // "="
		case OperatorIds.JML_EQUIV : // "<==>"
		case OperatorIds.JML_IMPLIES : //"==>"
		case OperatorIds.JML_REV_IMPLIES : // "<=="
		case OperatorIds.JML_NONNULLELEMENTS :  //"\\nonnullelements"
		case OperatorIds.JML_NOT_EQUIV : // "<=!=>"
		case OperatorIds.JML_OLD : // "\\old"
		case OperatorIds.JML_PRE : // "\\pre"
		default:
			throw new RuntimeException("FSPV: Operator in binary expression \"" + e + "\" is not supported"); //$NON-NLS-1$ //$NON-NLS-2$
		}
	}
	
	private TheoryType jdtType2TheoryType(TypeBinding type) {
		switch (type.id) {
		case TypeIds.T_int:
			return TheoryType.Int();
		case TypeIds.T_char:
			return TheoryType.Nat();
		case TypeIds.T_boolean:
			return TheoryType.Bool();
		case TypeIds.T_float:
		case TypeIds.T_double:
		case TypeIds.T_short:
		case TypeIds.T_byte:
		case TypeIds.T_long:
		default:
			throw new RuntimeException(type +" : not supported"); //$NON-NLS-1$
		}
	}
}