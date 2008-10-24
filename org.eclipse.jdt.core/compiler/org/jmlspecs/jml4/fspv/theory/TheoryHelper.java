package org.jmlspecs.jml4.fspv.theory;

import java.util.Stack;
import java.util.Vector;


public class TheoryHelper {
	private Stack blocks;
	private Stack expressions;
	private Vector lemmas;
	private Vector variables;
	
	public TheoryHelper() {
		this.blocks = new Stack();
		this.expressions = new Stack();
		this.lemmas = new Vector();
	}

	public void pushBlockStack() {
		this.blocks.push(new TheoryStack(TheoryStack.BLOCK));
	}

	public void pushLocalVarStack(TheoryVariable variable) {
		this.blocks.push(new TheoryStack(variable, TheoryStack.LOCALVAR));
	}

	public void pushLoopStack() {
		this.blocks.push(new TheoryStack(TheoryStack.LOOP));
	}
	
	public void push(TheoryStatement s) {
		((Stack) this.blocks.peek()).push(s);
	}
	
	public TheoryStatement popStatement() {
		TheoryStack s = (TheoryStack) this.blocks.peek();
		return (TheoryStatement) s.pop();
	}

	
	//FIXME: there is no need for all this.  This method should be simplified so as to:
	//       1) pop a statement stack
	//       2) create the block or Local block statement.
	//       3) return that block
	//TODO: A separate method should then be added that will just pop the top element of the top stack.
	public TheoryBlockStatement popStatements() {
		TheoryStack s = (TheoryStack) this.blocks.pop();
		// If this is a LOOP stack then we know it contains just top level
		// TheoryBlockStatement.
		TheoryStatement [] statements = new TheoryStatement[s.size()];
		for(int i=s.size()-1 ; i>=0 ; i--)
			statements[i] = (TheoryStatement) s.pop();
		TheoryBlockStatement block = null;
		if(s.isLocalVarStack())
			block = new TheoryLocalDeclarationBlockStatement(s.getVariable(),statements);
		else
			block = new TheoryBlockStatement(statements);
		return block;
	}
	
	public void push(TheoryExpression e) {
		this.expressions.push(e);
	}
	
	public TheoryExpression popExpression() {
		return (TheoryExpression) this.expressions.pop();
	}

	public boolean isTopStack() {
		return ((TheoryStack) this.blocks.peek()).isTopStack();
	}
	
	public boolean isLocalVarStack() {
		return ((TheoryStack) this.blocks.peek()).isLocalVarStack();
	}
	
	public boolean isBlockStack() {
		return ((TheoryStack) this.blocks.peek()).isBlockStack();
	}

	public void addLemma(TheoryLemma l) {
		this.lemmas.add(l);
	}
	
	public TheoryLemma [] getLemmas() {
		TheoryLemma [] retVal = new TheoryLemma[this.lemmas.size()];
		for(int i=0;i<retVal.length;i++) 
			retVal[i] = (TheoryLemma) this.lemmas.elementAt(i);
		return retVal;
	}
	
	public void addVariable(TheoryVariable v) {
		this.variables.add(v);
	}
	
	public TheoryVariable [] getVariables() {
		TheoryVariable [] retVal = new TheoryVariable[this.variables.size()];
		for(int i = 0;i< retVal.length; i++) 
			retVal[i] = (TheoryVariable) this.variables.elementAt(i);
		return retVal;
	}

	public TheoryVariable lookupVariable(TheoryVariable variable) {
		for(int i = 0;i<this.variables.size();i++) {
			TheoryVariable v = (TheoryVariable) this.variables.elementAt(i);
			if(v.equals(variable))
				return v;
		}
		throw new RuntimeException("Unable to find variable " + variable); //$NON-NLS-1$
	}	
	
	public void reset() {
		// Reset the variables.
		this.variables = new Vector();
		this.blocks.push(new TheoryStack(TheoryStack.TOP));
	}
	
	private class TheoryStack extends java.util.Stack {
		private static final long serialVersionUID = -3823549624894737674L;
		private static final byte TOP = 0;
		private static final byte BLOCK = 1;
		private static final byte LOCALVAR = 2;
		private static final byte LOOP = 3;
		private final byte type;
		private TheoryVariable variable;
		
		TheoryStack(byte type) {
			super();
			this.type = type;
		}

		TheoryStack(TheoryVariable variable, byte type) {
			this.variable = variable;
			this.type = type;
		}

		boolean isTopStack() {
			return this.type == TheoryStack.TOP;
		}
		
		boolean isLocalVarStack() {
			return this.type == TheoryStack.LOCALVAR;
		}
		
		boolean isBlockStack() {
			return this.type == TheoryStack.BLOCK;
		}
		
		boolean isLoopStack() {
			return this.type == TheoryStack.LOOP;
		}
		
		TheoryVariable getVariable() {
			return this.variable;
		}
		
	}

}
