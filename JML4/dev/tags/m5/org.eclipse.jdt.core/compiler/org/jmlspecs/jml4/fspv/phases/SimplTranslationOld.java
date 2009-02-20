package org.jmlspecs.jml4.fspv.phases;

import java.util.Stack;
import java.util.Vector;

import org.eclipse.jdt.internal.compiler.ast.OperatorIds;
import org.jmlspecs.jml4.fspv.theory.TheoryOperator;
import org.jmlspecs.jml4.fspv.theory.ast.Theory;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryArgument;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryAssignment;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryBlock;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryBooleanLiteral;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryCompoundAssignment;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryConstructorDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryFieldDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryIntLiteral;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryLocalDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryMethodDeclaration;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryOperatorIds;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryPostfixExpression;
import org.jmlspecs.jml4.fspv.theory.ast.TheorySingleNameReference;
import org.jmlspecs.jml4.fspv.theory.ast.TheoryVisitor;

public class SimplTranslationOld extends TheoryVisitor {

	private static final String	EMPTY	= ""; //$NON-NLS-1$
	private static final String	THEORY	= "theory"; //$NON-NLS-1$
	private static final String	IMPORTS	= "imports"; //$NON-NLS-1$
	private static final String	S	= " "; //$NON-NLS-1$
	private static final String	BEGIN	= "begin"; //$NON-NLS-1$
	private static final String	END	= "end"; //$NON-NLS-1$
	private static final String	T	= "  "; //$NON-NLS-1$
	private static final String	HOARE_STATE_NAME_SUFFIX	= "_vars"; //$NON-NLS-1$
	private static final String	EQUAL	= "="; //$NON-NLS-1$
	private static final String	HOARE_STATE	= "hoarestate"; //$NON-NLS-1$
	private static final String	LP	= "("; //$NON-NLS-1$
	private static final String	RP	= ")"; //$NON-NLS-1$
	private static final String	IN	= "in"; //$NON-NLS-1$
	private static final String	Q	= "\""; //$NON-NLS-1$
	private static final String	LEMMA	= "lemma"; //$NON-NLS-1$
	private static final String	COLON	= ":"; //$NON-NLS-1$
	private static final String	RBRACE	= "\\<rbrace>"; //$NON-NLS-1$
	private static final String	LBRACE	= "\\<lbrace>"; //$NON-NLS-1$
	private static final String	SEMI_SEMI	= ";;"; //$NON-NLS-1$
	private static final String	ASSIGNMENT	= ":=="; //$NON-NLS-1$
	private static final String	WHILE	= "WHILE"; //$NON-NLS-1$
	private static final String	DO	= "DO"; //$NON-NLS-1$
	private static final String	OD	= "OD"; //$NON-NLS-1$
	private static final String	AND	= "\\<and>"; //$NON-NLS-1$
	private static final String	INV	= "INV"; //$NON-NLS-1$
	private static final String	VAR	= "VAR"; //$NON-NLS-1$
	private static final String	MEASURE	= "MEASURE"; //$NON-NLS-1$
	private static final String	TURNSTILE	= "\\<turnstile>"; //$NON-NLS-1$
	private static final String	GAMMA	= "\\<Gamma>"; //$NON-NLS-1$
	private static final String	APPLY	= "apply"; //$NON-NLS-1$
	private static final String	VCG	= "vcg"; //$NON-NLS-1$
	private static final String	AUTO	= "auto"; //$NON-NLS-1$
	private static final String	IMP_LIST	= "HeapList Vcg"; //$NON-NLS-1$
	private static final String	DONE	= "done"; //$NON-NLS-1$
	private static final String	ACUTE	= "\\<acute>"; //$NON-NLS-1$
	private static final String LOC = "LOC"; //$NON-NLS-1$
	private static final String COL = "COL"; //$NON-NLS-1$
	private static final String IF = "IF"; //$NON-NLS-1$
	private static final String THEN = "THEN"; //$NON-NLS-1$
	private static final String ELSE = "ELSE"; //$NON-NLS-1$
	private static final String FI = "FI"; //$NON-NLS-1$
	private static final String P = "."; //$NON-NLS-1$
	private static final String GGREATER = "\\<ggreater>"; //$NON-NLS-1$
	private static final String NAT = "nat"; //$NON-NLS-1$
	private static final String PLUS = "+"; //$NON-NLS-1$
	private static final String ALGEBRA = "algebra"; //$NON-NLS-1$
	private static final String LB = "{"; //$NON-NLS-1$
	private static final String RB = "}"; //$NON-NLS-1$
	private static final String NL = "\n"; //$NON-NLS-1$
	private static final String GLOBALS = "globals_"; //$NON-NLS-1$
	private static final String MEMORY = "memory"; //$NON-NLS-1$
	private static final String COL_COL = "::"; //$NON-NLS-1$
	private static final String REF = "ref"; //$NON-NLS-1$
	private static final String EQGREATER = "=>"; //$NON-NLS-1$
	private static final String LIST = "list"; //$NON-NLS-1$
	private static final String ALLOC = "alloc"; //$NON-NLS-1$
	private static final String FREE = "free"; //$NON-NLS-1$
	private static final String FALSE = "False"; //$NON-NLS-1$
	private static final String TRUE = "True"; //$NON-NLS-1$
	private static final String SKIP = "skip"; //$NON-NLS-1$
	private static final String PROCEDURES = "procedures"; //$NON-NLS-1$
	private static final String COMMA = ", "; //$NON-NLS-1$
	private static final String JINT = "int"; //$NON-NLS-1$
	private static final String INT = "int"; //$NON-NLS-1$
	private static final String JBOOLEAN = "boolean"; //$NON-NLS-1$
	private static final String BOOL = "bool"; //$NON-NLS-1$
	private static final String WHERE = "where"; //$NON-NLS-1$
	private static final String ZERO = "0"; //$NON-NLS-1$
	private static final String RESULT = "result'"; //$NON-NLS-1$
	private static final String LSB = "["; //$NON-NLS-1$
	private static final String RSB = "]"; //$NON-NLS-1$
	private static final String PIPE = "|"; //$NON-NLS-1$
	private static final String SUBEXP = "SubExp"; //$NON-NLS-1$
	private static final String EQ = "="; //$NON-NLS-1$
	
	private static final String	LESS_EQUAL	= "\\<le>"; //$NON-NLS-1$
	private static final String	GREATER_EQUAL	= "\\<ge>"; //$NON-NLS-1$
	private static final String	NOT_EQUAL	= "\\<noteq>"; //$NON-NLS-1$
	private static final String	OR_OR	= "\\<or>";  //$NON-NLS-1$ //FIXME: Map to a conditional OR
	private static final String	AND_AND	= "\\<and>"; //$NON-NLS-1$ //FIXME: Map to a condition AND
	private static final String	MINUS	= "-"; //$NON-NLS-1$
	private static final String	NOT	= "\\<not>"; //$NON-NLS-1$
	private static final String	REMAINDER	= "mod"; //$NON-NLS-1$
	private static final String	MULTIPLY	= "*"; //$NON-NLS-1$
	private static final String	OR	= "\\<or>"; //$NON-NLS-1$
	private static final String	DIVIDE	= "div"; //$NON-NLS-1$
	private static final String	GREATER	= ">"; //$NON-NLS-1$
	private static final String	LESS	= "<"; //$NON-NLS-1$
	private static final String ONE = "1"; //$NON-NLS-1$
	private static final String THIS = "this"; //$NON-NLS-1$
	private static final String RIGHTARROW = "\\<rightarrow>"; //$NON-NLS-1$
	private static final String NEW = "NEW"; //$NON-NLS-1$
	private static final String SPEC = "_spec"; //$NON-NLS-1$
	private static final String FORALL = "\\<forall>"; //$NON-NLS-1$
	private static final String SIGMA = "\\<sigma>"; //$NON-NLS-1$
	private static final String PROC = "PROC"; //$NON-NLS-1$
	private static final String COLUMN = ":"; //$NON-NLS-1$

	private Tabber tabs;
	private Stack stack;
	public String thy;

	public SimplTranslationOld() {
		this.tabs = new Tabber();
		this.setStack(new Stack());
		this.thy = EMPTY;
	}

	public boolean visit(Theory theory) {
		//
		String result = this.header(theory.getName());
		result+=NL;
		this.tabs.addDepth();
		result+=this.memory();
		if(theory.fields != null) {
			result+=NL;
			result+=this.fieldsHeader(theory.getName());
			this.tabs.addDepth();
			String prefix = this.tabs.getWSPrefix();
			for(int i=0;i<theory.fields.length;i++) {
				theory.fields[i].traverse(this);
				result+=prefix + this.getStack().pop() + NL;
			}
			result+=NL;
			this.tabs.rmDepth();
		}
		if(theory.methods != null) {
			for(int i=0;i<theory.methods.length;i++) {
				theory.methods[i].traverse(this);
				result+=this.getStack().pop() + NL + NL;
			}
		}
		result += END;
		this.thy = result;
		return false;
	}
	
	public boolean visit(TheoryFieldDeclaration theoryFieldDeclaration) {
		String result = EMPTY;
		String type = this.javaType2SimplType(theoryFieldDeclaration.getType());
		if(theoryFieldDeclaration.isStatic())
			result = theoryFieldDeclaration.getName() + COL_COL + type;
		else
			result = theoryFieldDeclaration.getName() + COL_COL + Q + REF + EQGREATER + type + Q;
		// TODO: Deal with initializations
		if(theoryFieldDeclaration.initialization != null) {
			theoryFieldDeclaration.initialization.traverse(this);
		}
		this.getStack().push(result);
		return false;
	}

	public boolean visit(TheoryConstructorDeclaration theoryConstructorDeclaration) {
		/*
		 *  Arguments
		 */
		String flatArgs = EMPTY;
		if(theoryConstructorDeclaration.arguments != null) {
			String[] arguments = new String[theoryConstructorDeclaration.arguments.length];
			for(int i=0;i<theoryConstructorDeclaration.arguments.length;i++) {
				theoryConstructorDeclaration.arguments[i].traverse(this);
				arguments[i] = (String) this.getStack().pop();
			}
			flatArgs = this.flatten(arguments, COMMA);
		}
		/*
		 *  Local variables declared inside the constructor.
		 */
		String flatLocals = EMPTY;
		{
			String[] locals = new String[theoryConstructorDeclaration.locals.length];
			if(theoryConstructorDeclaration.hasLocals()) {
				for(int i=0;i<theoryConstructorDeclaration.locals.length;i++) {
					theoryConstructorDeclaration.locals[i].traverse(this);
					locals[i]= (String) this.getStack().pop();
				}
				flatLocals = this.tabs.getWSPrefix() + WHERE + this.flatten(locals, S) + IN + NL;
			}			
		}

		/*
		 * Statements
		 */
		Vector stmts = new Vector();
		
		// Obtain the instance fields of the class for this constructor so that we can use them
		// at Simpl's memory allocation statement.
		TheoryFieldDeclaration[] instanceFields = theoryConstructorDeclaration.enclosingTheory.getInstancefields();
		String fields=EMPTY;
		if(instanceFields.length > 0) {
			for(int i=0;i<instanceFields.length;i++) {
				if(i+1 == instanceFields.length)
					fields+=instanceFields[i].getName() + ASSIGNMENT + this.initValue(instanceFields[i].getType());
				else
					fields+=instanceFields[i].getName() + ASSIGNMENT + this.initValue(instanceFields[i].getType()) + COMMA;
			}
			stmts.add(ACUTE + RESULT + ASSIGNMENT + NEW + S + LP + instanceFields.length+COL_COL+NAT + RP + S + LSB + fields + RSB);
		}
		
		// Now go over the statements of the body and store them in the vector.
		if(theoryConstructorDeclaration.statements != null) {
			for(int i=0;i<theoryConstructorDeclaration.statements.length;i++) {
				theoryConstructorDeclaration.statements[i].traverse(this);
				stmts.add(this.getStack().pop());
			}
		}
		// Flatten the statements into a string separated by ";;\n"
		String flatStatements = EMPTY;
		{
			String[] strStmts = new String[stmts.size()];
			this.tabs.addDepth();
			String prefix = this.tabs.getWSPrefix();
			for(int i=0;i<stmts.size();i++)
				strStmts[i]=prefix + stmts.elementAt(i);
			this.tabs.rmDepth();
			flatStatements = this.flatten(strStmts, SEMI_SEMI + NL);
		}
		
		/*
		 *  Setup the procedures body of the procedure.
		 */
		String result = EMPTY;
		{
			String prefix = this.tabs.getWSPrefix();
			result+=prefix + PROCEDURES + S + theoryConstructorDeclaration.getName() + 
				LP + flatArgs + PIPE + THIS + COL_COL + REF + RP + NL;
			result+=flatLocals;
			result+=prefix + Q + NL;
			result+=flatStatements + NL;
			result+=prefix + Q + NL;
			result+=NL;
		}

		/*
		 *  Precondition
		 */
		String precondition = TRUE;
		if(theoryConstructorDeclaration.precondition != null) {
			theoryConstructorDeclaration.precondition.traverse(this);
			precondition = (String) this.getStack().pop();
		}

		/*
		 *  Postcondition
		 */
		String postcondition = TRUE;
		if(theoryConstructorDeclaration.postcondition != null) {
			theoryConstructorDeclaration.postcondition.traverse(this);
			postcondition = (String) this.getStack().pop();
		}
		
		// Get the prestate and the arguments for the body of the _spec lemma.
		String prestateHOLArgs = EMPTY;
		String prestateAssumptions = EMPTY;
		String bodyArguments = EMPTY;
		{
			if(theoryConstructorDeclaration.arguments != null) {
				PrestateVisitor pre = new PrestateVisitor();
				String[] holArguments = new String[theoryConstructorDeclaration.arguments.length];
				String[] assumptions = new String[theoryConstructorDeclaration.arguments.length];
				String[] bodyArgs = new String[theoryConstructorDeclaration.arguments.length];
				for(int i=0;i<theoryConstructorDeclaration.arguments.length;i++) {
					theoryConstructorDeclaration.arguments[i].traverse(pre);
					String name = (String) this.getStack().pop();
					holArguments[i] = name;
					assumptions[i] = name + S + EQ + S + ACUTE + name;
					bodyArgs[i] = ACUTE + name;
				}
				prestateHOLArgs = this.flatten(holArguments, S);
				prestateAssumptions = this.flatten(assumptions, S + AND + S);
				bodyArguments = this.flatten(bodyArgs, COMMA);
			}
		}
		
		// Generate the lemma.
		{
			String prefix = this.tabs.getWSPrefix();
			String locale = GLOBALS + theoryConstructorDeclaration.getEnclosingType();
			String lemmaName = theoryConstructorDeclaration.getName() + SPEC;
			result+= prefix + LEMMA + S + LP + IN + S + locale + RP + S + lemmaName + COLUMN + NL;
			prefix = this.tabs.addDepth();
			result+= prefix + Q + NL;
			result+= prefix + FORALL + SIGMA + S + prestateHOLArgs + P + NL;
			prefix = this.tabs.addDepth();
			//add the pre
			result+= prefix + LBRACE + S + prestateAssumptions + S + AND + S + precondition + S + RBRACE + NL;
			//add the body
			result+= prefix + ACUTE + THIS + S + ASSIGNMENT + S + PROC + S + theoryConstructorDeclaration.getName() + 
				LP + bodyArguments + RP + NL;
			//add the post
			result+= prefix + LBRACE + S + postcondition + S + RBRACE + NL;
			prefix = this.tabs.rmDepth();
			result+= prefix + Q + NL;
			result+= prefix + APPLY + LP + VCG + RP + NL;
			result+= prefix + APPLY + LP + AUTO + RP + NL;
			prefix = this.tabs.rmDepth();
			result+= prefix + DONE + NL;
		}
		this.getStack().push(result);
		return false;
	}

	public boolean visit(TheoryMethodDeclaration theoryMethodDeclaration) {
		String result = EMPTY;
		if(theoryMethodDeclaration.precondition != null) {
			theoryMethodDeclaration.precondition.traverse(this);
		}
		if(theoryMethodDeclaration.postcondition != null) {
			theoryMethodDeclaration.postcondition.traverse(this);
		}
		if(theoryMethodDeclaration.locals != null) {
			for(int i=0;i<theoryMethodDeclaration.locals.length;i++)
				theoryMethodDeclaration.locals[i].traverse(this);
		}
		if(theoryMethodDeclaration.statements != null) {
			for(int i=0;i<theoryMethodDeclaration.statements.length;i++)
				theoryMethodDeclaration.statements[i].traverse(this);
		}
		this.stack.push(result);
		return false;
	}

	public boolean visit(TheoryArgument theoryArgument) {
		String result = theoryArgument.getName() + COL_COL + theoryArgument.getType();
		this.getStack().push(result);
		return false;
	}
	
	public boolean visit(TheoryLocalDeclaration theoryLocalDeclaration) {
		String result = theoryLocalDeclaration.getName() + COL_COL + theoryLocalDeclaration.getType();
		this.getStack().push(result);
		return false;
	}
	
	public boolean visit(TheoryBlock theoryBlock) {
		String result = EMPTY;
		for(int i=0;i<theoryBlock.statements.length;i++) {
			theoryBlock.statements[i].traverse(this);
			result += this.getStack().pop() + SEMI_SEMI + NL;
		}
		this.getStack().push(result);
		return false;
	}

	public boolean visit(TheoryAssignment theoryAssignment) {
		theoryAssignment.left.traverse(this);
		String left = (String) this.getStack().pop();
		theoryAssignment.expression.traverse(this);
		String expr = (String) this.getStack().pop();
		if(theoryAssignment.isSubExpression())
			this.getStack().push(SUBEXP + LP + left + EQ + expr + RP);
		else
			this.getStack().push(left + ASSIGNMENT + expr);
		return false;
	}

	public boolean visit(TheoryCompoundAssignment theoryAssignment) {
		theoryAssignment.left.traverse(this);
		String left = (String) this.getStack().pop();
		theoryAssignment.expression.traverse(this);
		String expr = (String) this.getStack().pop();
		String op = this.simplOperator(theoryAssignment.getOperator());
		if(theoryAssignment.isSubExpression())
			this.getStack().push(SUBEXP + LP + left + op + EQ +  expr + RP);			
		else {
			this.getStack().push(left + ASSIGNMENT + left + op + expr);
		}
		return false;
	}


	public boolean visit(TheoryPostfixExpression theoryAssignment) {
		theoryAssignment.left.traverse(this);
		String left = (String) this.getStack().pop();
		String op = this.simplOperator(theoryAssignment.getOperator());
		if(theoryAssignment.isSubExpression())
			this.getStack().push(SUBEXP + LP + left + op + op + RP);
		else
			this.getStack().push(left + ASSIGNMENT + left + op + ONE);
		return false;
	}

	
	public boolean visit(TheoryIntLiteral theoryIntLiteral) {
		String result = LP+LP+INT+RP+theoryIntLiteral.toString()+RP;
		this.getStack().push(result);
		return false;
	}

	public boolean visit(TheoryBooleanLiteral theoryBooleanLiteral) {
		String result = EMPTY;
		if(theoryBooleanLiteral.isTrue())
			result = LP + TRUE + RP;
		else
			result = LP + FALSE + RP;
		this.getStack().push(result);
		return false;
	}
	
	
	public boolean visit(TheorySingleNameReference theorySingleNameReference) {
		String result = EMPTY;
		if(theorySingleNameReference.isField()) {
			result = LP + ACUTE + THIS + RIGHTARROW + ACUTE + theorySingleNameReference.toString() + RP;
		} else {
			result = LP + ACUTE + theorySingleNameReference.toString() + RP;			
		}
		this.getStack().push(result);
		return false;
	}

	///////////////////////////////////////////////////////////////////////
	/////////////////////////// Helper methods ////////////////////////////
	///////////////////////////////////////////////////////////////////////

	private String simplOperator(int operator) {
		switch(operator) {
		case TheoryOperatorIds.EQUAL_EQUAL : // "=="
			return EQ;
		case TheoryOperatorIds.LESS_EQUAL : // "<="
			return LESS_EQUAL;
		case TheoryOperatorIds.GREATER_EQUAL : // ">="
			return GREATER_EQUAL;
		case TheoryOperatorIds.NOT_EQUAL : // "!="
			return NOT_EQUAL;
		case TheoryOperatorIds.OR_OR : // "||"
			return OR_OR;
		case TheoryOperatorIds.AND_AND : // "&&"
			return AND_AND;
		case TheoryOperatorIds.PLUS : // "+"
			return PLUS;
		case TheoryOperatorIds.MINUS : // "-"
			return MINUS;
		case TheoryOperatorIds.NOT : // "!"
			return NOT;
		case TheoryOperatorIds.REMAINDER : // "%"
			return REMAINDER;
		case TheoryOperatorIds.AND : //"&"
			return AND;
		case TheoryOperatorIds.MULTIPLY :  //"*"
			return MULTIPLY;
		case TheoryOperatorIds.OR : // "|"
			return OR;
		case TheoryOperatorIds.DIVIDE : // "/"
			return DIVIDE;
		case TheoryOperatorIds.GREATER :  // ">"
			return GREATER;
		case TheoryOperatorIds.LESS : //"<"
			return LESS;

		case TheoryOperatorIds.QUESTIONCOLON : //"?:"
			//			return TheoryOperator.QuestionColon();
		case TheoryOperatorIds.LEFT_SHIFT : //"<<"
		case TheoryOperatorIds.RIGHT_SHIFT : //">>"
		case TheoryOperatorIds.UNSIGNED_RIGHT_SHIFT : // ">>>"
		case TheoryOperatorIds.XOR : // "^"
		case TheoryOperatorIds.TWIDDLE : // "~"
		case TheoryOperatorIds.EQUAL : // "="
		case TheoryOperatorIds.JML_EQUIV : // "<==>"
		case TheoryOperatorIds.JML_IMPLIES : //"==>"
		case TheoryOperatorIds.JML_REV_IMPLIES : // "<=="
		case TheoryOperatorIds.JML_NONNULLELEMENTS :  //"\\nonnullelements"
		case TheoryOperatorIds.JML_NOT_EQUIV : // "<=!=>"
		case TheoryOperatorIds.JML_OLD : // "\\old"
		case TheoryOperatorIds.JML_PRE : // "\\pre"
		}
		return null;	
	}	

	
	private String memory() {
		String prefix = this.tabs.getWSPrefix();
		String result = prefix + HOARE_STATE + S + GLOBALS + MEMORY + S + NL;
		this.tabs.addDepth(); prefix = this.tabs.getWSPrefix();
		result += prefix + ALLOC + COL_COL + Q + REF + S + LIST + Q + NL;
		result += prefix + FREE + COL_COL + NAT + NL;
		this.tabs.rmDepth();
		return result;
	}

	private String fieldsHeader(String name) {
		String prefix = this.tabs.getWSPrefix();
		String result=prefix + HOARE_STATE + S + GLOBALS + name + EQUAL + NL; 
		return result;
	}

	private String header(String name) {
		String prefix = this.tabs.getWSPrefix();
		String result = prefix + THEORY + S + name + S + IMPORTS + S + IMP_LIST + S + BEGIN + NL;
		return result;
	}

	private String flatten(String[] arr, String sep) {
		String result = EMPTY;
		for(int i = 0;i<arr.length;i++) {
			if(i+1 == arr.length)
				result += arr[i];
			else
				result += arr[i] + sep;
		}
		return result;
	}

	private String javaType2SimplType(String type) {
		String result = EMPTY;
		if(type.equals(JINT))
			result = INT;
		else if(type.equals(JBOOLEAN))
			result = BOOL;
		return result;
	}
	
	private String initValue(String type) {
		String result = EMPTY;
		if(type.equals(JINT))
			result = ZERO;
		else if(type.equals(JBOOLEAN))
			result = TRUE;
		return result;	
	}

	public void setStack(Stack stack) {
		this.stack = stack;
	}

	public Stack getStack() {
		return stack;
	}

	class Tabber {
		private int			depth = 0;
		private String 	wsPrefix = EMPTY;
		
		String rmDepth() {
			this.depth--;
			this.setWSPrefix();
			return this.getWSPrefix();
		}

		String addDepth() {
			this.depth++;
			this.setWSPrefix();
			return this.getWSPrefix();
		}

		private void setWSPrefix() {
			this.wsPrefix=EMPTY;
			for(int i=0;i<this.depth;i++)	this.wsPrefix+=T;
		}

		String getWSPrefix() {
			return this.wsPrefix;
		}
	}

	class PrestateVisitor extends TheoryVisitor {

		public boolean visit(TheoryArgument theoryArgument) {
			String result = theoryArgument.getName();
			SimplTranslationOld.this.getStack().push(result);
			return false;
		}

	}

}
