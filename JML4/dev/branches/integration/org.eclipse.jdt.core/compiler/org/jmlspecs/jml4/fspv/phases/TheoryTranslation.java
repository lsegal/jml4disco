package org.jmlspecs.jml4.fspv.phases;

import java.util.Stack;
import java.util.Vector;

import org.eclipse.jdt.internal.compiler.ast.AllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.BinaryExpression;
import org.eclipse.jdt.internal.compiler.ast.Block;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;
import org.eclipse.jdt.internal.compiler.ast.ConstructorDeclaration;
import org.eclipse.jdt.internal.compiler.ast.EqualExpression;
import org.eclipse.jdt.internal.compiler.ast.ExplicitConstructorCall;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.FalseLiteral;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.ast.IntLiteral;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MessageSend;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.NullLiteral;
import org.eclipse.jdt.internal.compiler.ast.PostfixExpression;
import org.eclipse.jdt.internal.compiler.ast.ReturnStatement;
import org.eclipse.jdt.internal.compiler.ast.SingleNameReference;
import org.eclipse.jdt.internal.compiler.ast.SingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;
import org.jmlspecs.jml4.ast.JmlAssignment;
import org.jmlspecs.jml4.ast.JmlClause;
import org.jmlspecs.jml4.ast.JmlCompilationUnitDeclaration;
import org.jmlspecs.jml4.ast.JmlConstructorDeclaration;
import org.jmlspecs.jml4.ast.JmlLoopAnnotations;
import org.jmlspecs.jml4.ast.JmlLoopInvariant;
import org.jmlspecs.jml4.ast.JmlLoopVariant;
import org.jmlspecs.jml4.ast.JmlMethodDeclaration;
import org.jmlspecs.jml4.ast.JmlOldExpression;
import org.jmlspecs.jml4.ast.JmlResultReference;
import org.jmlspecs.jml4.ast.JmlWhileStatement;
import org.jmlspecs.jml4.fspv.TraceAstVisitor;
import org.jmlspecs.jml4.fspv.theory.ast.Theory;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryAllocationExpression;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryArgument;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryAssignment;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryBinaryExpression;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryBlock;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryBooleanLiteral;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryCompoundAssignment;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryConstructorDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryEqualExpression;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryExpression;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryFieldDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryFieldReference;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryIntLiteral;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryLiteral;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryLocalDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryMessageSend;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryMethodDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryNullLiteral;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryOldExpression;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryPostfixExpression;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryResultReference;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryReturnStatement;
import org.jmlspecs.jml4.fspv.theory.ast.TheorySingleNameReference;
import org.jmlspecs.jml4.fspv.theory.ast.TheorySkipStatement;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryStatement;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryWhileStatement;
import org.jmlspecs.jml4.util.Logger;

public class TheoryTranslation extends TraceAstVisitor {

	private final Stack stack;
	private Vector locals;
	private Vector methods;
	private Vector fields;

	public Theory theory;

	public TheoryTranslation() {
		this.stack=new Stack();
	}

	///////////////////////////////////////////////////////////////////
	//////////////// Compilation Unit - Top level node ////////////////
	///////////////////////////////////////////////////////////////////

	public boolean visit(JmlCompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(JmlCompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	// This is needed because of the manner JmlCompilationUnitDeclaration.traverse() is defined
	// i.e., by making use of super() that invokes the parent class's overwritten method.
	// Maybe what is needed is the copy the CompilationUnitDeclaration traverse method into the JML's one.
	public boolean visit(CompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(CompilationUnitDeclaration compilationUnitDeclaration, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	///////////////////////////////////////////////////////////////////
	//////////////////////////// Types ////////////////////////////////
	///////////////////////////////////////////////////////////////////
	public boolean visit(SingleTypeReference singleTypeReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(SingleTypeReference singleTypeReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Type Declaration--usually for Class types
	public boolean visit(TypeDeclaration typeDeclaration, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());

		this.theory = new Theory(typeDeclaration);
		
		this.fields=new Vector();
		this.methods=new Vector();

		// Traverse through fields--the Theory AST nodes will be stored into the fields vector.
		if (typeDeclaration.fields != null) {
			int length = typeDeclaration.fields.length;
			for (int i = 0; i < length; i++) {
				FieldDeclaration field;
				if ((field = typeDeclaration.fields[i]).isStatic()) {
					typeDeclaration.traverse(this, typeDeclaration.staticInitializerScope);
				} else {
					field.traverse(this, typeDeclaration.initializerScope);
				}
			}
		}

		// Create an array from the fields vector.
		TheoryFieldDeclaration[] fs = new TheoryFieldDeclaration[this.fields.size()];
		for(int i=0;i<fs.length;i++)
			fs[i] = (TheoryFieldDeclaration) this.fields.elementAt(i);

		// Traverse through methods--the Theory AST nodes will be stored into the lemmas vector.
		if (typeDeclaration.methods != null) {
			int length = typeDeclaration.methods.length;
			for (int i = 0; i < length; i++)
				typeDeclaration.methods[i].traverse(this, typeDeclaration.scope);
		}

		// Create an array from the lemmas vector.
		TheoryMethodDeclaration[] ms = new TheoryMethodDeclaration[this.methods.size()];
		for(int i=0;i<ms.length;i++)
			ms[i] = (TheoryMethodDeclaration) this.methods.elementAt(i);

		// Update the fields + methods.
		this.theory.fields = fs;
		this.theory.methods = ms;

		return false;
	}
	public void endVisit(TypeDeclaration typeDeclaration, CompilationUnitScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	///////////////////////////////////////////////////////////////////
	////////////////////////// Class Members //////////////////////////
	///////////////////////////////////////////////////////////////////

	// Constructors
	public boolean visit(JmlConstructorDeclaration constructorDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString()); 
		// initialize the vector storing local variable declarations
		this.locals = new Vector();

		//Specification
		TheoryExpression pre = TheoryBooleanLiteral.makeTrue(this.theory);
		TheoryExpression post= TheoryBooleanLiteral.makeTrue(this.theory);
		if (constructorDeclaration.specification != null) {
			//precondition
			Expression precondition = constructorDeclaration.specification.getPrecondition();
			if(precondition != null) {
				precondition.traverse(this, constructorDeclaration.scope);
				pre =  (TheoryExpression) this.stack.pop();
			}
			//postcondition
			Expression postcondition = constructorDeclaration.specification.getPostcondition();
			if(postcondition != null) {
				postcondition.traverse(this, constructorDeclaration.scope);
				post =  (TheoryExpression) this.stack.pop();
			}
		}

		// arguments
		TheoryArgument[] args = new TheoryArgument[0];
		if (constructorDeclaration.arguments != null) {
			int argumentLength = constructorDeclaration.arguments.length;
			args = new TheoryArgument[argumentLength];
			for (int i = 0; i < argumentLength; i++) {
				constructorDeclaration.arguments[i].traverse(this, constructorDeclaration.scope);
				args[i] = (TheoryArgument) this.stack.pop();
			}
		}

		// TODO: Add support for exceptions--the code below is cut-n-paste from the traverse method.
		if (constructorDeclaration.thrownExceptions != null) {
			int thrownExceptionsLength = constructorDeclaration.thrownExceptions.length;
			for (int i = 0; i < thrownExceptionsLength; i++)
				constructorDeclaration.thrownExceptions[i].traverse(this, constructorDeclaration.scope);
		}

		// statements
		TheoryStatement[] statements = new TheoryStatement[0];
		if (constructorDeclaration.statements != null) {
			int statementsLength = constructorDeclaration.statements.length;
			statements = new TheoryStatement[statementsLength];
			for (int i = 0; i < statementsLength; i++) {
				constructorDeclaration.statements[i].traverse(this, constructorDeclaration.scope);
				statements[i] = (TheoryStatement) this.stack.pop();
			}
		}

		// local variables
		TheoryLocalDeclaration[] localDecls = new TheoryLocalDeclaration[this.locals.size()];
		for(int i=0;i<localDecls.length;i++)
			localDecls[i] = (TheoryLocalDeclaration) this.locals.elementAt(i);

		// Create the theory node
		TheoryConstructorDeclaration constructor = 
			new TheoryConstructorDeclaration(constructorDeclaration, this.theory, pre, post, args, localDecls, statements);

		// Add the lemma to vector of lemmas.
		this.methods.add(constructor);

		return false;
	}
	public void endVisit(JmlConstructorDeclaration constructorDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public boolean visit(ConstructorDeclaration constructorDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(ConstructorDeclaration constructorDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Field Declaration
	public boolean visit(FieldDeclaration fieldDeclaration, MethodScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(FieldDeclaration fieldDeclaration, MethodScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression initialization = null;
		if(fieldDeclaration.initialization != null)
			initialization = (TheoryExpression) this.stack.pop();
		TheoryFieldDeclaration s = new TheoryFieldDeclaration(fieldDeclaration, this.theory, initialization);
		// Add the local variable declaration into the locals vector.
		this.fields.add(s);
	}

	// Methods
	public boolean visit(JmlMethodDeclaration methodDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());

		// initialize the vector storing local variable declarations
		this.locals = new Vector();

		//Specification
		TheoryExpression pre = TheoryBooleanLiteral.makeTrue(this.theory);
		TheoryExpression post= TheoryBooleanLiteral.makeTrue(this.theory);
		if (methodDeclaration.specification != null) {
			//precondition
			Expression precondition = methodDeclaration.specification.getPrecondition();
			if(precondition != null) {
				precondition.traverse(this, methodDeclaration.scope);
				pre = (TheoryExpression) this.stack.pop();
			}
			//postcondition
			Expression postcondition = methodDeclaration.specification.getPostcondition();
			if(postcondition != null) {
				postcondition.traverse(this, methodDeclaration.scope);
				post =  (TheoryExpression) this.stack.pop();
			}
		}

		// arguments
		TheoryArgument[] args = new TheoryArgument[0];
		if (methodDeclaration.arguments != null) {
			int argumentLength = methodDeclaration.arguments.length;
			args = new TheoryArgument[argumentLength];
			for (int i = 0; i < argumentLength; i++) {
				methodDeclaration.arguments[i].traverse(this, methodDeclaration.scope);
				args[i] = (TheoryArgument) this.stack.pop();
			}
		}

		// TODO: Add support for exceptions--the code below is cut-n-paste from the traverse method.
		if (methodDeclaration.thrownExceptions != null) {
			int thrownExceptionsLength = methodDeclaration.thrownExceptions.length;
			for (int i = 0; i < thrownExceptionsLength; i++)
				methodDeclaration.thrownExceptions[i].traverse(this, methodDeclaration.scope);
		}

		// statements
		TheoryStatement[] statements = new TheoryStatement[0];
		if (methodDeclaration.statements != null) {
			int statementsLength = methodDeclaration.statements.length;
			statements = new TheoryStatement[statementsLength];
			for (int i = 0; i < statementsLength; i++) {
				methodDeclaration.statements[i].traverse(this, methodDeclaration.scope);
				statements[i] = (TheoryStatement) this.stack.pop();
			}
		}

		// local variables
		TheoryLocalDeclaration[] localDecls = new TheoryLocalDeclaration[this.locals.size()];
		for(int i=0;i<localDecls.length;i++)
			localDecls[i] = (TheoryLocalDeclaration) this.locals.elementAt(i);

		TheoryMethodDeclaration method = 
			new TheoryMethodDeclaration(methodDeclaration, this.theory, pre, post, args, localDecls, statements);

		// Add the lemma to vector of lemmas.
		this.methods.add(method);

		return false;
	}

	public void endVisit(JmlMethodDeclaration methodDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	public boolean visit(MethodDeclaration methodDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(MethodDeclaration methodDeclaration, ClassScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	///////////////////////////////////////////////////////////////////
	/////////////////////////// Statements ////////////////////////////
	///////////////////////////////////////////////////////////////////

	// arguments
	public boolean visit(Argument argument, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(Argument argument, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryArgument a = new TheoryArgument(argument, this.theory);
		this.stack.push(a);
	}

	public boolean visit(Block block, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(Block block, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryStatement [] statements = new TheoryStatement[0];
		if(block.statements != null) {
			statements = new TheoryStatement[block.statements.length];
			for(int i=0;i<statements.length;i++)
				statements[statements.length-i-1] = (TheoryStatement) this.stack.pop();
		}
		TheoryBlock s = new TheoryBlock(block, this.theory, statements);
		this.stack.push(s);
	}

	// locals
	public boolean visit(LocalDeclaration localDeclaration, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(LocalDeclaration localDeclaration, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression initialization = null;
		if(localDeclaration.initialization != null)
			initialization = (TheoryExpression) this.stack.pop();
		TheoryLocalDeclaration s = new TheoryLocalDeclaration(localDeclaration, this.theory, initialization);
		// Add the local variable declaration into the locals vector.
		this.locals.add(s);
		this.stack.push(s);
	}

	// return
	public boolean visit(ReturnStatement returnStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(ReturnStatement returnStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression expression = (TheoryExpression) this.stack.pop();
		TheoryReturnStatement s = new TheoryReturnStatement(returnStatement, this.theory, expression);
		this.stack.push(s);
	}

	// super();
	// this();
	// TODO: Add support when required.  For now do nothing.
	public boolean visit(ExplicitConstructorCall explicitConstructor, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return false;
	}
	public void endVisit(ExplicitConstructorCall explicitConstructor, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// while
	// The reason for not depending on the traverse method is that there exists none.
	// The reason for not creating one is because code already exists at this point
	// that may break.
	public boolean visit(JmlWhileStatement whileStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		// Condition
		whileStatement.condition.traverse(this, scope);
		TheoryExpression condition = (TheoryExpression) this.stack.pop();
		// Action--i.e., while loop body.
		TheoryStatement action = new TheorySkipStatement(whileStatement.action, this.theory);
		if (whileStatement.action != null) {
			whileStatement.action.traverse(this, scope);
			action = (TheoryStatement) this.stack.pop();
		}
		// Loop Annotations
		TheoryExpression [] invariants = new TheoryExpression[0];
		TheoryExpression [] variants = new TheoryExpression[0];
		if(whileStatement.annotations != null) {
			//Invariants
			JmlLoopInvariant [] invs = whileStatement.annotations.invariants;
			invariants = new TheoryExpression[invs.length];
			for(int i=0;i<invs.length;i++) {
				invs[i].traverse(this, scope);
				TheoryExpression e = (TheoryExpression) this.stack.pop();
				invariants[i] = e;
			}
			//Variants
			JmlLoopVariant [] vars = whileStatement.annotations.variants;
			variants = new TheoryExpression[vars.length];
			for (int i = 0; i < vars.length; i++) {
				vars[i].traverse(this, scope);
				TheoryExpression e = (TheoryExpression) this.stack.pop();
				variants[i] = e;
			}
		}
		TheoryWhileStatement s = new TheoryWhileStatement(whileStatement, this.theory, condition, action, invariants, variants);
		this.stack.push(s);
		return false;
	}
	public void endVisit(JmlWhileStatement whileStatement, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}


	///////////////////////////////////////////////////////////////////
	/////////////////////////// Expressions ///////////////////////////
	///////////////////////////////////////////////////////////////////

	// allocation
	public boolean visit(AllocationExpression allocationExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(AllocationExpression allocationExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression [] arguments = new TheoryExpression[0];
		if(allocationExpression.arguments != null) {
			arguments = new TheoryExpression[allocationExpression.arguments.length];
			for(int i=0;i<arguments.length;i++)
				arguments[arguments.length-i-1]=(TheoryExpression) this.stack.pop();
		}
//		TheoryTypeReference typeRef = (TheoryTypeReference) this.stack.pop();
		TheoryAllocationExpression e = new TheoryAllocationExpression(allocationExpression, this.theory, arguments);
		this.stack.push(e);
	}

	// assignment
	public boolean visit(JmlAssignment assignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(JmlAssignment assignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}
	public boolean visit(Assignment assignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(Assignment assignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression expression = (TheoryExpression) this.stack.pop();
		TheoryExpression left = (TheoryExpression) this.stack.pop();
		TheoryAssignment e = new TheoryAssignment(assignment, this.theory, left, expression);
		this.stack.push(e);
	}

	// binary
	public boolean visit(BinaryExpression binaryExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(BinaryExpression binaryExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression right = (TheoryExpression) this.stack.pop();
		TheoryExpression left  = (TheoryExpression) this.stack.pop();
		TheoryBinaryExpression e = new TheoryBinaryExpression(binaryExpression, this.theory, right, left);
		this.stack.push(e);
	}

	// compound assignment
	public boolean visit(CompoundAssignment compoundAssignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(CompoundAssignment compoundAssignment, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression expression = (TheoryExpression) this.stack.pop();
		TheoryExpression left = (TheoryExpression) this.stack.pop();
		TheoryCompoundAssignment e = new TheoryCompoundAssignment(compoundAssignment, this.theory, left, expression);
		this.stack.push(e);
	}

	// equal
	public boolean visit(EqualExpression equalExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(EqualExpression equalExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression right = (TheoryExpression) this.stack.pop();
		TheoryExpression left  = (TheoryExpression) this.stack.pop();
		TheoryEqualExpression e = new TheoryEqualExpression(equalExpression, this.theory, right, left);
		this.stack.push(e);
	}

	// message
	public boolean visit(MessageSend messageSend, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(MessageSend messageSend, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression [] arguments = new TheoryExpression[messageSend.arguments.length];
		for(int i=0;i<arguments.length;i++) {
			arguments[arguments.length-i-1]=(TheoryExpression) this.stack.pop();
		}
		TheoryExpression receiver = (TheoryExpression) this.stack.pop();
		TheoryMessageSend e = new TheoryMessageSend(messageSend, this.theory, receiver, arguments);
		this.stack.push(e);
	}

	// postfix i++,i--
	public boolean visit(PostfixExpression postfixExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(PostfixExpression postfixExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression lhs = (TheoryExpression) this.stack.pop();
		TheoryPostfixExpression e = new TheoryPostfixExpression(postfixExpression, this.theory, lhs);
		this.stack.push(e);
	}

	// SingleNameReference
	public boolean visit(SingleNameReference singleNameReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); 
		TheorySingleNameReference sNameRef = new TheorySingleNameReference(singleNameReference, this.theory);
		this.stack.push(sNameRef);
		return false;
	}
	public void endVisit(SingleNameReference singleNameReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// FieldReference
	public boolean visit(FieldReference fieldReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); 
		TheoryFieldReference e = new TheoryFieldReference(fieldReference, this.theory);
		this.stack.push(e);
		return false;
	}


	///////////////////////////////////////////////////////////////////
	///////////////////////////  Literal //////////////////////////////
	///////////////////////////////////////////////////////////////////

	// int
	public boolean visit(IntLiteral intLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); 
		TheoryLiteral l = new TheoryIntLiteral(intLiteral, this.theory);
		this.stack.push(l);
		return false;
	}
	public void endVisit(IntLiteral intLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Boolean True
	public boolean visit(TrueLiteral trueLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); 
		this.stack.push(new TheoryBooleanLiteral(trueLiteral, this.theory));
		return false;
	}
	public void endVisit(TrueLiteral trueLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Boolean False
	public boolean visit(FalseLiteral falseLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); 
		this.stack.push(new TheoryBooleanLiteral(falseLiteral, this.theory));
		return false;
	}
	public void endVisit(FalseLiteral falseLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	public boolean visit(NullLiteral nullLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); 
		TheoryNullLiteral e = new TheoryNullLiteral(nullLiteral, this.theory);
		this.stack.push(e);
		return false;
	}
	public void endVisit(NullLiteral nullLiteral, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}


	///////////////////////////////////////////////////////////////////
	///////////////////////////  JML  /////////////////////////////////
	///////////////////////////////////////////////////////////////////

	public boolean visit(JmlClause jmlClause, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());return true;
	}
	public void endVisit(JmlClause jmlClause, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

	// Loop Annotations
	public boolean visit(JmlLoopAnnotations jmlLoopAnnotations, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
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

	public boolean visit(JmlOldExpression jmlOldExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString()); return true;
	}
	public void endVisit(JmlOldExpression jmlOldExpression, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryExpression expression = (TheoryExpression) this.stack.pop();
		TheoryOldExpression e = new TheoryOldExpression(jmlOldExpression, this.theory, expression);
		this.stack.push(e);
	}

	public boolean visit(JmlResultReference resultReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
		TheoryResultReference e = new TheoryResultReference(resultReference, this.theory);
		this.stack.push(e);
		return false;
	}
	public void endVisit(JmlResultReference resultReference, BlockScope scope) {
		Logger.printlnWithTrace(0, this.toString());
	}

}
