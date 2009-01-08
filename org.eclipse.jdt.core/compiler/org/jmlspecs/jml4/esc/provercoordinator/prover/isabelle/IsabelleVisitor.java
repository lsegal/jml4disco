package org.jmlspecs.jml4.esc.provercoordinator.prover.isabelle;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcAnd;
import org.jmlspecs.jml4.esc.vc.lang.VcAndNary;
import org.jmlspecs.jml4.esc.vc.lang.VcArithExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcArrayAllocationExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcArrayReference;
import org.jmlspecs.jml4.esc.vc.lang.VcBooleanConstant;
import org.jmlspecs.jml4.esc.vc.lang.VcConditionalExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcFieldReference;
import org.jmlspecs.jml4.esc.vc.lang.VcFieldStore;
import org.jmlspecs.jml4.esc.vc.lang.VcIntegerConstant;
import org.jmlspecs.jml4.esc.vc.lang.VcLogicalExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcNot;
import org.jmlspecs.jml4.esc.vc.lang.VcOperator;
import org.jmlspecs.jml4.esc.vc.lang.VcOr;
import org.jmlspecs.jml4.esc.vc.lang.VcQuantifiedExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcQuantifier;
import org.jmlspecs.jml4.esc.vc.lang.VcRelativeExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcSuperReference;
import org.jmlspecs.jml4.esc.vc.lang.VcThisReference;
import org.jmlspecs.jml4.esc.vc.lang.VcVarDecl;
import org.jmlspecs.jml4.esc.vc.lang.VcVariable;

public class IsabelleVisitor extends ProverVisitor {

	private static final String NOT_IMPLEMENTED = "implement me"; //$NON-NLS-1$
	private static final char ISABELLE_SEP = '_';
	private final String theoryName;
	private String proof;

	public IsabelleVisitor(String filename) {
		int pos = filename.lastIndexOf(File.separatorChar);
		if (pos < 0)
			pos = filename.lastIndexOf('/');
		this.theoryName = pos >= 0
		                ? filename.substring(pos+1)
		                : filename;
	}

	public String visit(VcBooleanConstant vcBooleanConstant) {
		return ((vcBooleanConstant.value) ? "True" : "False"); //$NON-NLS-1$ //$NON-NLS-2$
	}

	public String visitAsTerm(VcBooleanConstant vcBooleanConstant) {
		return this.visit(vcBooleanConstant);
	}

	public String visit(VcIntegerConstant intConst) {
		return "(" + intConst.value + " :: int)"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public String visit(VcVariable var) {
		String name = var.name + POS_SEP + var.pos + INC_SEP + var.incarnation;
//			(this.duplicateVariables.contains(var)
//				    ? var.name + POS_SEP + var.pos + INC_SEP + var.incarnation
//					: var.name +                     INC_SEP + var.incarnation);
		return "(" + name + "::" + getType(var) + ")";   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
	}

	public String visit(VcAnd vcAnd) {
		return "(" + vcAnd.left.accept(this) + " & " + vcAnd.right.accept(this) + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public String visit(VcLogicalExpression vc) {
		String operator = getOperator(vc.operator, vc.type);
		if (vc.operator == VcOperator.IMPLIES && vc.left instanceof VcAndNary)
			operator = ""; //$NON-NLS-1$
		String left = vc.left.accept(this);
		String right = vc.right.accept(this);
		if (vc.operator == VcOperator.IMPLIES && vc.left.endsInImpliesTrue())
			return right;
		
		return "(" + left + " " + operator + " " + right + ")"; //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

	public String visit(VcOr vcOr) {
		return "(" + vcOr.left.accept(this) + " | " + vcOr.right.accept(this) + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public String visit(VcRelativeExpression eq) {
		return "(" + eq.left.accept(this) + " " + getOperator(eq.operator, eq.left.type) + " " + eq.right.accept(this) + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

	private String getOperator(VcOperator op, TypeBinding type) {
		if (op == VcOperator.EQUALS || op == VcOperator.EQUIV) {
			return "="; //$NON-NLS-1$
		} else if (op == VcOperator.NOT_EQUALS || op == VcOperator.NOT_EQUIV) {
			return "~="; //$NON-NLS-1$
		} else if (op == VcOperator.IMPLIES) {
			return "-->"; //$NON-NLS-1$
		} else if (op == VcOperator.DIVIDE) {
			return "div"; //$NON-NLS-1$
		} else if (op == VcOperator.REMAINDER) {
			return "mod"; //$NON-NLS-1$
		} else {
			return op.name;
		}
	}

	public String visit(VcConditionalExpression condExpr) {
		String cond = condExpr.condition.accept(this);
		String ifTrue = condExpr.valueIfTrue.accept(this);
		String ifFalse = condExpr.valueIfFalse.accept(this);
		return "(if " + cond + " then " + ifTrue + " else " + ifFalse + " )"; //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

	public String visitAsTerm(VcConditionalExpression vcConditionalExpression) {
		return visit(vcConditionalExpression);
	}

	public String visit(VcNot vcNot) {
		return "(~ " + vcNot.vc.accept(this) + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public String visit(VcVarDecl vcVarDecl, int max) {
		String isabelleType = getType(vcVarDecl);
		StringBuffer allIncarnations = new StringBuffer();
		for (int i = 0; i <= max; i++) {
			allIncarnations.append("  " + (vcVarDecl.name + ISABELLE_SEP + i) + " :: " +  //$NON-NLS-1$ //$NON-NLS-2$
					isabelleType + "\n"); //$NON-NLS-1$
		}
		return allIncarnations.toString();
	}

	private static final Map typesMap = new HashMap();
	static {
		typesMap.put(TypeBinding.BOOLEAN, "bool"); //$NON-NLS-1$
		typesMap.put(TypeBinding.CHAR, "int"); //$NON-NLS-1$
		typesMap.put(TypeBinding.BYTE, "int"); //$NON-NLS-1$
		typesMap.put(TypeBinding.SHORT, "int"); //$NON-NLS-1$
		typesMap.put(TypeBinding.INT, "int"); //$NON-NLS-1$
		typesMap.put(TypeBinding.LONG, "int"); //$NON-NLS-1$
	}

	public String visit(VcArithExpression arithExpr) {
		String decls = arithExpr.visitVarDecls(this);
		String left = arithExpr.left.accept(this);
		String op = getOperator(arithExpr.operator, arithExpr.type);
		String right = arithExpr.right.accept(this);
		return decls + "((" + left + ") " + op + " (" + right + "))"; //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$//$NON-NLS-4$
	}

	public String visit(VcSuperReference superRef) {
		throw new RuntimeException(NOT_IMPLEMENTED);
	}

	public String visit(VcThisReference thisRef) {
		throw new RuntimeException(NOT_IMPLEMENTED);
	}

	public String visit(VcFieldReference fieldRef) {
		throw new RuntimeException(NOT_IMPLEMENTED);
	}

	public String visit(VcFieldStore fieldStore) {
		throw new RuntimeException(NOT_IMPLEMENTED);
	}

	public String visit(VcArrayReference arrayRef) {
		throw new RuntimeException("implement me");
	}

	public String visit(VcArrayAllocationExpression vcArrayAllocationExpression) {
		throw new RuntimeException("implement me");
	}

	public String visit(VcQuantifiedExpression expr) {
		String op = getQuantifier(expr.quantifier);
		String translation;
		if (expr.quantifier.isLogical()) {
			return getLogicalQuantifiedTranslation(expr, op);
		} else {
			Utils.assertTrue(expr.quantifier.isNumeric(), "expecting a numeric quantifier but was '"+expr.quantifier+"'"); //$NON-NLS-1$ //$NON-NLS-2$
			translation = getNumericQuantifiedTranslation(expr, op);
			return translation;
		}
	}

	private String getLogicalQuantifiedTranslation(VcQuantifiedExpression expr,
			String op) {
		String translation;
		String body = expr.body.accept(this);
		String joiner = op.equals("ALL") ? "-->" : "&";   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		String range = expr.range.accept(this);

		boolean rangeIsConstantTrue = expr.range.equals(VcBooleanConstant.TRUE);
		String rangeJoinerBody = (rangeIsConstantTrue)
							   ? rangeJoinerBody = body
							   : range + " " + joiner + " " + body;  //$NON-NLS-1$//$NON-NLS-2$

		VcVarDecl[] boundVarDecls = (expr.isBlock)
		                          ? expr.boundVarDecls()
		                          : (VcVarDecl[])expr.range.decls().toArray(VcVarDecl.EMPTY);
		
		if (boundVarDecls.length == 0) {
			Utils.assertTrue(rangeIsConstantTrue, "expected range to be the constant True"); //$NON-NLS-1$
			translation = body;
		} else {
			String vars = translateBoundVars(boundVarDecls);
			translation = "(" + op + vars + " . (" + rangeJoinerBody + "))";    //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		}
		return translation;
	}

	//@ requires expr.quantifier.isNumeric();
	private String getNumericQuantifiedTranslation(VcQuantifiedExpression expr, String op) {
	    List boundVarDecls = expr.range.decls();
		String vars = translateBoundVars((VcVarDecl[]) boundVarDecls.toArray(VcVarDecl.EMPTY));
		String[] bounds = getBounds(expr.range);
		String trans = (bounds == null)
		             ? translateNumericQuantifiedTranslationToComprehension(expr, op, vars)
		             : translateNumericQuantifiedTranslationToRange(expr, op, vars, bounds);
		return trans;
	}

	//@ requires expr.quantifier.isNumeric();
	private String translateNumericQuantifiedTranslationToComprehension(VcQuantifiedExpression expr, String op, String vars) {
		String range = expr.range.accept(this);
		String body = expr.body.accept(this);
		String compOp = (op.equals("sum")) //$NON-NLS-1$
		              ? "\\<Sum>" //$NON-NLS-1$
		              : "\\<Prod>"; //$NON-NLS-1$
		String trans = "("+compOp+" { "+body+" | "+vars+" . "+range+"})";    //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$//$NON-NLS-4$ //$NON-NLS-5$
		return trans;
	}
	
	//@ requires expr.quantifier.isNumeric();
	private /*@nullable*/ String translateNumericQuantifiedTranslationToRange(VcQuantifiedExpression expr, String op, String vars, String[] bounds) {
		Utils.assertNotNull(bounds, "bounds is null"); //$NON-NLS-1$
		String lower = bounds[0];
		String upper = bounds[1];
		String body = expr.body.accept(this);
		if (bounds.length == 3)
			body = "(let "+bounds[2]+" in "+body+")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		String trans = "(" + op + " " + lower + " " + upper + " (% "+vars+" . " + body + "))";    //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$//$NON-NLS-4$ //$NON-NLS-5$ //$NON-NLS-6$
		return trans;
	}

	private /*@nullable*/ String[] getBounds(VC range) {
		if (range instanceof VcConditionalExpression)
			return getBoundsFromConditionalExpression((VcConditionalExpression)range);
		else if (range instanceof VcAnd)
			return getBoundsFromAnd((VcAnd)range);
		else if (range instanceof VcLogicalExpression)
			return getBoundsFromLogicalExpression((VcLogicalExpression)range);
		else
			return null;
	}

	private String[] getBoundsFromLogicalExpression(VcLogicalExpression range) {
		if (range.operator == VcOperator.IMPLIES) {
			range.left.addDecls(range.decls());
			String[] fromLeft = getBounds(range.left);
			String fromRight = range.right.accept(this);
			if (fromLeft == null || fromLeft[0] == null || fromLeft[1] == null)
				return null;
			return new String[]{fromLeft[0], fromLeft[1], fromRight};
		}
		return null;
	}

	private /*@nullable*/ String[] getBoundsFromConditionalExpression(VcConditionalExpression range) {
	    List boundVarDecls = range.getVarDecls();
	    if (boundVarDecls == null || boundVarDecls.size() != 1)
	    	return null;
	    VcVarDecl boundVar = (VcVarDecl) boundVarDecls.get(0);
		VC rangeLeft  = range.condition;
		VC rangeRight = range.valueIfTrue;
		VC falseConst = range.valueIfFalse;
		if (!(falseConst instanceof VcBooleanConstant))
			return null;
		if (((VcBooleanConstant)falseConst).value)
			return null;
		String lower = getLowerBound(boundVar, rangeLeft);
		String upper = getUpperBound(boundVar, rangeRight);
		String[] bounds = (lower == null || upper == null)
        				? null
        				: new String[]{lower, upper};
		return bounds;
	}
	private /*@nullable*/ String[] getBoundsFromAnd(VcAnd range) {
	    List boundVarDecls = range.getVarDecls();
	    if (boundVarDecls == null || boundVarDecls.size() != 1)
	    	return null;
	    VcVarDecl boundVar = (VcVarDecl) boundVarDecls.get(0);
		VC rangeLeft  = range.left;
		VC rangeRight = range.right;
		String lower = getLowerBound(boundVar, rangeLeft);
		String upper = getUpperBound(boundVar, rangeRight);
		String[] bounds = (lower == null || upper == null)
						? null
						: new String[]{lower, upper};
		return bounds;
	}

	private String getLowerBound(VcVarDecl boundVar, VC rangeLeft) {
		if (!(rangeLeft instanceof VcRelativeExpression))
			return null;
		VcRelativeExpression range = (VcRelativeExpression) rangeLeft;
		VcOperator op = range.operator;
		if (op != VcOperator.LESS && op != VcOperator.LESS_EQUALS)
			return null;
		if (!(range.right instanceof VcVariable))
			return null;
		VcVariable var = (VcVariable) range.right;
		if (! (var.name.equals(boundVar.name) && var.pos == boundVar.pos))
			return null;
		boolean isLessThan = (op == VcOperator.LESS);
		String trans = range.left.accept(this);
		if (isLessThan)
			trans = "("+trans+" + 1)"; //$NON-NLS-1$ //$NON-NLS-2$
		return trans;
	}

	private String getUpperBound(VcVarDecl boundVar, VC rangeRight) {
		if (!(rangeRight instanceof VcRelativeExpression))
			return null;
		VcRelativeExpression range = (VcRelativeExpression) rangeRight;
		VcOperator op = range.operator;
		if (op != VcOperator.LESS && op != VcOperator.LESS_EQUALS)
			return null;
		if (!(range.left instanceof VcVariable))
			return null;
		VcVariable var = (VcVariable) range.left;
		if (! (var.name.equals(boundVar.name) && var.pos == boundVar.pos))
			return null;
		boolean isLessThan = (op == VcOperator.LESS);
		String trans = range.right.accept(this);
		if (isLessThan)
			trans = "("+trans+" - 1)"; //$NON-NLS-1$ //$NON-NLS-2$
		return trans;
	}

	public String visitAsTerm(VcQuantifiedExpression expr) {
		return this.visit(expr);
	}

	private String getQuantifier(VcQuantifier quantifier) {
		if (quantifier.isForall())
			return "ALL"; //$NON-NLS-1$
		if (quantifier.isExists())
			return "EX"; //$NON-NLS-1$
		if (quantifier.isSum())
			return "sum"; //$NON-NLS-1$
		if (quantifier.isProduct())
			return "product"; //$NON-NLS-1$
		if (quantifier.isMin())
			return "min"; //$NON-NLS-1$
		if (quantifier.isMax())
			return "max"; //$NON-NLS-1$
		if (quantifier.isNumOf())
			return "num_of"; //$NON-NLS-1$
		Utils.assertTrue(false, "'"+quantifier.lexeme+"' not implemented yet"); //$NON-NLS-1$ //$NON-NLS-2$
		return null;
	}

	private String translateBoundVars(VcVarDecl[] boundVarDecls) {
		StringBuffer result = new StringBuffer();
		Set/*<String>*/ set = new HashSet/*<String>*/();
		for (int i = 0; i < boundVarDecls.length; i++) {
			VcVarDecl var = boundVarDecls[i];
			String name = var.name + POS_SEP + var.pos + ZERO_INCARNATION;
			String type = getType(var);
			if (! set.contains(name)) {
				result.append(" (" + name + "::" + type + ")"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
				set.add(name);
			}
		}
		return result.toString();
	}

	private String getType(TypeBinding type) {
		String mappedType = (String) typesMap.get(type);
		String isabelleType = mappedType == null ? type.debugName()
				                                 : mappedType;
		return isabelleType;
	}
	private String getType(VcVarDecl var) {
		return getType(var.type);
	}
	private String getType(VcVariable var) {
		return getType(var.type);
	}

	public String visitAsTerm(VcRelativeExpression vcRelativeExpression) {
		return visit(vcRelativeExpression);
	}

	public String visitAsTerm(VcAnd vcAnd) {
		return visit(vcAnd);
	}

	public String visitAsTerm(VcLogicalExpression vcImplies) {
		return visit(vcImplies);
	}

	public String visitAsTerm(VcOr vcOr) {
		return visit(vcOr);
	}

	public String visitAsTerm(VcNot vcNot) {
		return visit(vcNot);
	}

	public String visitAsTerm(VcVariable vcVariable) {
		return visit(vcVariable);
	}

	public String getTheory(VC vc, Map incarnations) {
		Utils.assertNotNull(this.proof);
		StringBuffer result = new StringBuffer();
		String lemma = vc.accept(this);
		result.append("theory " + this.theoryName + "\nimports UBP\nbegin\n"); //$NON-NLS-1$ //$NON-NLS-2$
		result.append("\nlemma main: \"" + lemma + "\" \n" + this.proof + "\n"); //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
		result.append("\nend\n"); //$NON-NLS-1$
		return result.toString().replace('@', ISABELLE_SEP).replace('$', ISABELLE_SEP);
	}

	public void setProofMethodTo(String proof) {
		this.proof = proof;
	}

	public String visit(VcAndNary vcAndNary) {
		StringBuffer conjuncts = new StringBuffer();
		for (int i = 0; i < vcAndNary.conjuncts.length; i++) {
			if (i > 0)
				conjuncts.append("; "); //$NON-NLS-1$
			conjuncts.append(vcAndNary.conjuncts[i].accept(this));
		}
		return "[| " + conjuncts + "|] ==> "; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
