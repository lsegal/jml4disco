package org.jmlspecs.jml4.fspv;

import org.jmlspecs.jml4.fspv.theory.Theory;
import org.jmlspecs.jml4.fspv.theory.TheoryAssignmentStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryBinaryExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryBindStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryBlockStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryConditionalStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryLemma;
import org.jmlspecs.jml4.fspv.theory.TheoryLiteral;
import org.jmlspecs.jml4.fspv.theory.TheoryLocalDeclarationBlockStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryOperator;
import org.jmlspecs.jml4.fspv.theory.TheoryQuantifiedExpression;
import org.jmlspecs.jml4.fspv.theory.TheoryStatement;
import org.jmlspecs.jml4.fspv.theory.TheoryTempVariableReference;
import org.jmlspecs.jml4.fspv.theory.TheoryVariable;
import org.jmlspecs.jml4.fspv.theory.TheoryVariableReference;
import org.jmlspecs.jml4.fspv.theory.TheoryVisitor;
import org.jmlspecs.jml4.fspv.theory.TheoryWhileStatement;

public class SimplTranslator extends TheoryVisitor {

	private static final String	EMPTY	= ""; //$NON-NLS-1$
	private static final String	THEORY	= "theory"; //$NON-NLS-1$
	private static final String	L	= "\n"; //$NON-NLS-1$
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
	private static final String	IMP_LIST	= "Vcg"; //$NON-NLS-1$
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
	
	private int			depth = 0;
	private String 	wsPrefix = EMPTY;
	
	public Object accept(Theory theory) {
		String retVal=EMPTY;
		retVal += THEORY + S + theory.name + S + IMPORTS + S + IMP_LIST + S + L; 
		retVal += BEGIN + L;
		for(int i=0;i<theory.lemmas.length;i++){
			retVal+=theory.lemmas[i].visit(this)+L;
		}
		retVal+=END;
		return retVal;
	}

	public Object accept(TheoryLemma lemma) {
		String retVal=EMPTY;
		this.addDepth();
		// Set the HoareState
		String hsName = lemma.name + HOARE_STATE_NAME_SUFFIX;
		retVal+=wsPrefix + HOARE_STATE + S + hsName + S + EQUAL + L;
		this.addDepth();
		retVal+=this.processVariables(lemma.variables);
		this.rmDepth();
		// Set the lemma
		String inHsName = LP + IN + S + hsName +RP;
		retVal += wsPrefix + LEMMA + S + inHsName + S + lemma.name + COLON + S + Q + L;
		retVal += wsPrefix + GAMMA + S + TURNSTILE + L;
		this.addDepth();
		retVal += wsPrefix + LBRACE + S + lemma.pre.visit(this) + S + RBRACE + L;
		retVal += this.processStatements(lemma.block.statements);
		retVal += wsPrefix + LBRACE + S + lemma.post.visit(this) + S + RBRACE + L;
		retVal += wsPrefix + Q + L;
		retVal += wsPrefix + APPLY + LP + VCG + RP + L;
		retVal += wsPrefix + APPLY + LP + AUTO + RP + L;
		retVal += wsPrefix + APPLY + LP + ALGEBRA + RP + PLUS + L;
		this.rmDepth();
		retVal += wsPrefix + DONE + L;
		this.rmDepth();
		return retVal;
	}

	public Object accept(TheoryLocalDeclarationBlockStatement local) {
		String retVal = EMPTY;
		retVal+=wsPrefix + LOC + S + ACUTE + local.variable.name;
		retVal+=(local.variable.initialization!=null) ? S + ASSIGNMENT + S + local.variable.initialization.visit(this) + SEMI_SEMI + L : SEMI_SEMI + L;
		this.addDepth();
		retVal+=this.processStatements(local.statements);
		this.rmDepth();
		retVal+=wsPrefix + COL;
		return retVal;
	}
	
	private void rmDepth() {
		this.depth--;
		this.setWSPrefix();
	}

	private void addDepth() {
		this.depth++;
		this.setWSPrefix();		
	}

	private String processStatements(TheoryStatement[] statements) {
		String retVal = EMPTY;
		for(int i=0;i<statements.length;i++) {
			if (statements[i] != null) {
				retVal += statements[i].visit(this);
				if(statements[i] instanceof TheoryBindStatement)
					retVal += L;
				else
					retVal += (i == statements.length-1) ? L : SEMI_SEMI + L;
			}
		}
		return retVal;
	}

	private String processVariables(TheoryVariable[] variables) {
		String retVal=EMPTY;
		for(int i=0;i<variables.length; i++)
			if(! variables[i].isBound())
				retVal+=wsPrefix + variables[i].visit(this) + L;
		return retVal;
	}

	private void setWSPrefix() {
		this.wsPrefix=EMPTY;
		for(int i=0;i<this.depth;i++)	this.wsPrefix+=T;
	}

	public Object accept(TheoryVariable variable) {
		String retVal = EMPTY;
		retVal+=variable.toString();
		return retVal;
	}

	public Object accept(TheoryConditionalStatement c) {
		String retVal = EMPTY;
		retVal += wsPrefix + IF + S + c.condition.visit(this) + L;
		retVal += wsPrefix + THEN + L;
		this.addDepth();
		retVal += this.processStatements(c.thenBlock.statements);
		this.rmDepth();
		if(c.elseBlock != TheoryBlockStatement.EMPTY_BLOCK) {
			retVal += wsPrefix + ELSE + L;
			this.addDepth();
			retVal += this.processStatements(c.elseBlock.statements);
			this.rmDepth();
		}
		retVal += wsPrefix + FI;
		return retVal;
	}
	
	public Object accept(TheoryWhileStatement w) {
		String retVal = EMPTY;
		retVal += wsPrefix + WHILE + S + w.condition.visit(this) + L;
		retVal += this.processInvariants(w.loopAnnotations.invariant.expressions); 
		retVal += this.processVariants(w.loopAnnotations.variant.expressions);
		retVal += wsPrefix + DO + L;
		this.addDepth();
		retVal += this.processStatements(w.block.statements);
		this.rmDepth();
		retVal += wsPrefix + OD;
		return retVal;
	}

	public Object accept(TheoryBindStatement theoryBindStatement) {
		String result = EMPTY;
		int storedDepth = this.depth;
		this.depth = 1;this.rmDepth();
		String a = (String) theoryBindStatement.assignment.visit(this);
		this.depth = storedDepth-1;this.addDepth();
		String name = theoryBindStatement.tempVariableReference.variable.getDecoratedName();
		result += wsPrefix + ACUTE + name + S + GGREATER + S + theoryBindStatement.tempVariableReference + P + S + a + S + GGREATER;
		return result;
	}	

	
	private String processVariants(TheoryExpression[] variants) {
		String retVal = EMPTY;
		// Either one or no variant will be present.
		if(variants.length == 1) {
			String nat = EMPTY;
			TheoryExpression e = variants[0];
			if(e.type.isInt())
				nat = NAT;
			String variant = (String) variants[0].visit(this);
			retVal += wsPrefix + VAR + S + MEASURE + S + nat + S + variant + L;
		}
		return retVal;
	}

	private String processInvariants(TheoryExpression[] invariants) {
		String retVal = EMPTY;
		String conjunct = EMPTY;
		for(int i=0;i<invariants.length;i++) {
			conjunct += invariants[i].visit(this);
			conjunct += (i == invariants.length-1) ? EMPTY : S + AND + S;
		}
		if(invariants.length >0)
			retVal += wsPrefix + INV + S + LBRACE + S + conjunct + S + RBRACE + L;
		return retVal;
	}

	public Object accept(TheoryAssignmentStatement a) {
		String retVal = EMPTY;
		retVal += wsPrefix + a.lhs.visit(this) + S + ASSIGNMENT + S + a.rhs.visit(this);
		return retVal;
	}

	public Object accept(TheoryBinaryExpression e) {
		String retVal = EMPTY;
		retVal += LP + e.lhs.visit(this) + S + e.op.visit(this) + S + e.rhs.visit(this) + RP ;
		return retVal;
	}

	public Object accept(TheoryLiteral theoryLiteral) {
		return theoryLiteral.toString();
	}

	public Object accept(TheoryVariableReference theoryVariableReference) {
		if(theoryVariableReference.variable.isBound())
			return theoryVariableReference.toString();
		else
			return ACUTE + theoryVariableReference.toString();
	}
	
	public Object accept(TheoryTempVariableReference theoryTempVariableReference) {
		return theoryTempVariableReference.toString();
	}


	public Object accept(TheoryOperator theoryOperator) {
		return theoryOperator.toString();
	}	
	
	public Object accept(TheoryQuantifiedExpression theoryQuantifiedExpression) {
		String retVal = EMPTY;
		String variable = theoryQuantifiedExpression.variable.toString();
		String range = (String) theoryQuantifiedExpression.range.visit(this);
		retVal+= LP + theoryQuantifiedExpression.quantifier + S + LB + variable + P + S + range + S + RB + RP;
		return retVal;
	}

	
}
