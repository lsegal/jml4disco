package org.jmlspecs.jml4.fspv.phases;

import java.util.Stack;
import java.util.Vector;

import org.jmlspecs.jml4.fspv.simpl.ast.SimplArgument;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplBoolType;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplGlobalVariable;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplHoareState;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplIntType;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplLocalVariables;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplMapType;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplProcedure;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplProofObligation;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplRefType;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplState;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplStatement;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplTheory;
import org.jmlspecs.jml4.fspv.simpl.ast.SimplType;
import org.jmlspecs.jml4.fspv.theory.ast.Theory;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryArgument;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryConstructorDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryFieldDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryMethodDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryVisitor;

public class SimplTranslation extends TheoryVisitor {

	private Stack stack;
	public SimplTheory thy;

	public SimplTranslation() {
		this.stack = new Stack();
		this.thy = new SimplTheory();
	}


	public boolean visit(Theory theory) {

		// Fields
		SimplState state = null;
		if(theory.fields != null) {
			SimplGlobalVariable[] fields = new SimplGlobalVariable[theory.fields.length];
			for(int i=0;i<theory.fields.length;i++) {
				theory.fields[i].traverse(this);
				fields[i] = (SimplGlobalVariable) this.stack.pop();
			}
			state = new SimplHoareState(theory.getName(),fields,
					SimplHoareState.MEMORY);
		}

		// Methods
		SimplProofObligation[] pos = null;
		if(theory.methods != null) {
			pos = new SimplProofObligation[theory.methods.length];
			for(int i=0;i<theory.methods.length;i++) {
				theory.methods[i].traverse(this);
				pos[i] = (SimplProofObligation) this.stack.pop();
			}
		}

		// Set the Simpl theory attributes.
		this.thy.state = state;
		this.thy.pos = pos;

		return false;
	}
	
	/*
	 * Methods
	 * @see org.jmlspecs.jml4.fspv.theory.ast.TheoryVisitor#visit(org.jmlspecs.jml4.fspv.theory.ast.TheoryMethodDeclaration)
	 */
	public boolean visit(TheoryMethodDeclaration theoryMethodDeclaration) {
		if(theoryMethodDeclaration.precondition != null) {
			theoryMethodDeclaration.precondition.traverse(this);
		}
		if(theoryMethodDeclaration.postcondition != null) {
			theoryMethodDeclaration.postcondition.traverse(this);
		}
		if(theoryMethodDeclaration.arguments != null) {
			for(int i=0;i<theoryMethodDeclaration.arguments.length;i++)
				theoryMethodDeclaration.arguments[i].traverse(this);
		}
		if(theoryMethodDeclaration.locals != null) {
			for(int i=0;i<theoryMethodDeclaration.locals.length;i++)
				theoryMethodDeclaration.locals[i].traverse(this);
		}
		if(theoryMethodDeclaration.statements != null) {
			for(int i=0;i<theoryMethodDeclaration.statements.length;i++)
				theoryMethodDeclaration.statements[i].traverse(this);
		}
		return false;
	}


	/*
	 * Constructors
	 * @see org.jmlspecs.jml4.fspv.theory.ast.TheoryVisitor#visit(org.jmlspecs.jml4.fspv.theory.ast.TheoryConstructorDeclaration)
	 */
	public boolean visit(TheoryConstructorDeclaration theoryConstructorDeclaration) {
//		if(theoryConstructorDeclaration.precondition != null) {
//			theoryConstructorDeclaration.precondition.traverse(this);
//		}
//		if(theoryConstructorDeclaration.postcondition != null) {
//			theoryConstructorDeclaration.postcondition.traverse(this);
//		}

		// Arguments
		SimplArgument[] args = null;
		if(theoryConstructorDeclaration.arguments != null) {
			args = new SimplArgument[theoryConstructorDeclaration.arguments.length];
			for(int i=0;i<theoryConstructorDeclaration.arguments.length;i++) {
				theoryConstructorDeclaration.arguments[i].traverse(this);
				args[i] = (SimplArgument) this.stack.pop();
			}
		}
		
		SimplLocalVariables[] locals = null;
		if(theoryConstructorDeclaration.locals != null) {
			locals = new SimplLocalVariables[theoryConstructorDeclaration.locals.length];
			for(int i=0;i<theoryConstructorDeclaration.locals.length;i++) {
				theoryConstructorDeclaration.locals[i].traverse(this);
				locals[i] = (SimplLocalVariables) this.stack.pop();
			}
		}
		
		Vector statements = new Vector();
		if(theoryConstructorDeclaration.statements != null) {
			for(int i=0;i<theoryConstructorDeclaration.statements.length;i++) {
				theoryConstructorDeclaration.statements[i].traverse(this);
				statements.add(this.stack.pop());
			}
		}
		SimplStatement[] ss = new SimplStatement[statements.size()];
		for(int i=0;i<ss.length;i++)
			ss[i] = (SimplStatement) statements.elementAt(i);
		
		String name = "";
		SimplProcedure proc = new SimplProcedure(name, this.thy.state, args, locals, ss);
		
		return false;
	}

	public boolean visit(TheoryArgument theoryArgument) {
		
		return false;
	}

	
	/*
	 * Fields
	 * @see org.jmlspecs.jml4.fspv.theory.ast.TheoryVisitor#visit(org.jmlspecs.jml4.fspv.theory.ast.TheoryFieldDeclaration)
	 */
	public boolean visit(TheoryFieldDeclaration theoryFieldDeclaration) {

		String name = theoryFieldDeclaration.getName();
		SimplType type = this.translateType(theoryFieldDeclaration);
		if(! theoryFieldDeclaration.isStatic())
			type = new SimplMapType(new SimplRefType(), type);

		SimplGlobalVariable result = new SimplGlobalVariable(name, type);
		this.stack.push(result);

		return false;
	}


	private SimplType translateType(TheoryFieldDeclaration theoryFieldDeclaration) {
		SimplType result = null;
		if(theoryFieldDeclaration.isIntType())
			result = new SimplIntType();
		else if(theoryFieldDeclaration.isBooleanType())
			result = new SimplBoolType();
		else if(theoryFieldDeclaration.isClassType())
			result = new SimplRefType();
		else
			throw new RuntimeException("Unsupported type:" + theoryFieldDeclaration.toString()); //$NON-NLS-1$

		return result;
	}


}
