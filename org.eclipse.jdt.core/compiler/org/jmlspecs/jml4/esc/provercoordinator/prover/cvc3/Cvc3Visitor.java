package org.jmlspecs.jml4.esc.provercoordinator.prover.cvc3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;
import org.jmlspecs.jml4.esc.util.Counter;
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

public class Cvc3Visitor extends ProverVisitor {

	private static final char CVC_SEP = '$';
	private final Counter counter = new Counter();
	private final StringBuffer extra = new StringBuffer();

	public String visit(VcBooleanConstant vcBooleanConstant) {
		return ((vcBooleanConstant.value) ? "TRUE" : "FALSE"); //$NON-NLS-1$ //$NON-NLS-2$
	}

	public String visitAsTerm(VcBooleanConstant vcBooleanConstant) {
		return this.visit(vcBooleanConstant);
	}

	public String visit(VcIntegerConstant intConst) {
		return "" + intConst.value; //$NON-NLS-1$
	}

	public String visit(VcVariable vcVariable) {
		return vcVariable.name + POS_SEP + vcVariable.pos + INC_SEP + vcVariable.incarnation;
	}

	public String visit(VcAnd vcAnd) {
		return "(" + vcAnd.left.accept(this) + " AND " + vcAnd.right.accept(this) + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public String visit(VcLogicalExpression vcExpr) {
		String left  = vcExpr.left.accept(this);
		String right = vcExpr.right.accept(this);
		String op = null;

		if (vcExpr.operator==VcOperator.IMPLIES) {
			op = "=>"; //$NON-NLS-1$
		}
		if (vcExpr.operator==VcOperator.EQUIV) {
			op = "<=>"; //$NON-NLS-1$
		}
		if (op != null)
			return "(" + left + " "+op+" " + right + ")"; //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$

		Utils.assertTrue(vcExpr.operator==VcOperator.NOT_EQUIV, "unknown logical operator '"+vcExpr.operator+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		return "(NOT (" + left + " <=> " + right + "))"; //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
	}

	public String visit(VcOr vcOr) {
		return "(" + vcOr.left.accept(this) + " OR " + vcOr.right.accept(this) + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public String visit(VcRelativeExpression eq) {
		return "(" + eq.left.accept(this) + " " + getOperator(eq.operator.name, eq.left.type) + " " + eq.right.accept(this) + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

	private String getOperator(String name, TypeBinding type) {
		if (name.equals("==")) { //$NON-NLS-1$
			if (type == TypeBinding.BOOLEAN)
				return "<=>"; //$NON-NLS-1$
			else
				return "="; //$NON-NLS-1$
		} else if (name.equals("!=")) { //$NON-NLS-1$
			return "/="; //$NON-NLS-1$
		} else {
			return name;
		}
	}

	public String visit(VcConditionalExpression condExpr) {
		String cond = condExpr.condition.accept(this);
		String ifTrue = condExpr.valueIfTrue.accept(this);
		String ifFalse = condExpr.valueIfFalse.accept(this);
		return "(IF " + cond + " THEN " + ifTrue + " ELSE " + ifFalse + " ENDIF)"; //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

	public String visitAsTerm(VcConditionalExpression vcConditionalExpression) {
		return visit(vcConditionalExpression);
	}

	public String visit(VcNot vcNot) {
		return "(NOT " + vcNot.vc.accept(this) + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public String visit(VcQuantifiedExpression expr) {
		String op = getQuantifier(expr.quantifier);
		if (expr.quantifier.isLogical()) {
			String joiner = op.equals("FORALL") ? "=>" : "AND";   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
			String range = expr.range.accept(this);
			String body = expr.body.accept(this);
			List/*<VcVarDecl>*/ boundVars = new ArrayList/*<VcVarDecl>*/();
			boundVars.addAll(expr.range.decls());
			boundVars.addAll(expr.body.decls());
			if (boundVars.isEmpty()) {
				Utils.assertTrue(expr.range.equals(VcBooleanConstant.TRUE), "expected range to be the constant True"); //$NON-NLS-1$
				return body;
			}
			String vars = translateBoundVars(boundVars);
			String result = "(" + op + " (" + vars + ") : (" + range + " " + joiner + " " + body + "))";    //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$//$NON-NLS-4$ //$NON-NLS-5$ //$NON-NLS-6$
			return result;
		} else {
			Utils.assertTrue(expr.quantifier.isNumeric(), "expecting a numerical quantifier but was '"+op+"'"); //$NON-NLS-1$ //$NON-NLS-2$
			String var = op + CVC_SEP + this.counter.getAndIncCounter();
			String type = getType(expr.type);
			this.extra.append(var + " : " + type + " ;\n");  //$NON-NLS-1$//$NON-NLS-2$
			return var;
		}
	}

	public String visitAsTerm(VcQuantifiedExpression expr) {
		return this.visit(expr);
	}

	private String getQuantifier(VcQuantifier quantifier) {
		if (quantifier.isForall())
			return "FORALL"; //$NON-NLS-1$
		if (quantifier.isExists())
			return "EXISTS"; //$NON-NLS-1$
		if (quantifier.isSum())
			return "SUM"; //$NON-NLS-1$
		if (quantifier.isProduct())
			return "PRODUCT"; //$NON-NLS-1$
		if (quantifier.isMin())
			return "MIN"; //$NON-NLS-1$
		if (quantifier.isMax())
			return "MAX"; //$NON-NLS-1$
		if (quantifier.isNumOf())
			return "NUM_OF"; //$NON-NLS-1$
		return null;
	}

	private String translateBoundVars(List varDecls) {
		StringBuffer result = new StringBuffer();
		boolean firstTime = true;
		for (Iterator iterator = varDecls.iterator(); iterator.hasNext();) {
			VcVarDecl var = (VcVarDecl) iterator.next();
			String name = var.name + POS_SEP + var.pos + ZERO_INCARNATION;
			String type = getType(var.type);
			if (firstTime) {
				firstTime = false;
			} else {
				result.append(", "); //$NON-NLS-1$
			}
			result.append(name + ":" + type); //$NON-NLS-1$
		}
		return result.toString();
	}

	public String visit(VcVarDecl vcVarDecl, int max) {
		String cvcType = getType(vcVarDecl.type);
		StringBuffer allIncarnations = new StringBuffer();
		for (int i = 0; i <= max; i++) {
			if (i > 0)
				allIncarnations.append(", "); //$NON-NLS-1$
			allIncarnations.append(vcVarDecl.name + POS_SEP + vcVarDecl.pos + INC_SEP + i);
		}
		return allIncarnations.toString() + " : " + cvcType + " ;\n"; //$NON-NLS-1$//$NON-NLS-2$
	}

	private String getType(TypeBinding type) {
		String mappedType = (String) typesMap.get(type);
		String cvcType = mappedType == null ? type.debugName()
				: mappedType;
		return cvcType;
	}

	private static final Map typesMap = new HashMap();
	static {
		typesMap.put(TypeBinding.BOOLEAN, "BOOLEAN"); //$NON-NLS-1$
		typesMap.put(TypeBinding.CHAR, "INT"); //$NON-NLS-1$
		typesMap.put(TypeBinding.BYTE, "INT"); //$NON-NLS-1$
		typesMap.put(TypeBinding.SHORT, "INT"); //$NON-NLS-1$
		typesMap.put(TypeBinding.INT, "INT"); //$NON-NLS-1$
		typesMap.put(TypeBinding.LONG, "INT"); //$NON-NLS-1$
		typesMap.put(TypeBinding.FLOAT, "REAL"); //$NON-NLS-1$
		typesMap.put(TypeBinding.DOUBLE, "REAL"); //$NON-NLS-1$
	}

	public String visit(VcArithExpression arithExpr) {
		String decls = arithExpr.visitVarDecls(this);
		String left = arithExpr.left.accept(this);
		String op = arithExpr.operator.name;
		String right = arithExpr.right.accept(this);
		String trans = (op.equals("%"))  //$NON-NLS-1$
                     ? "mod("+left+", "+right+")"  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
                     : "((" + left + ") " + op + " (" + right + "))";   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$ //$NON-NLS-4$
		return decls + trans;
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
		StringBuffer result = new StringBuffer();
		String varDecls = getVarDecls(new VC[]{vc}, incarnations);
		String lemma = vc.accept(this);
		result.append(varDecls);
		result.append(this.extra.toString());
		this.extra.setLength(0);
		result.append("mod: (INT, INT) -> INT;\n\n"); //$NON-NLS-1$
		result.append("QUERY ( " + lemma + " );\n");  //$NON-NLS-1$//$NON-NLS-2$
		return result.toString().replace(INC_SEP, CVC_SEP).replace(POS_SEP, CVC_SEP);
	}

	public String visit(VcSuperReference superRef) {
		throw new RuntimeException("implement me");
	}

	public String visit(VcThisReference thisRef) {
		throw new RuntimeException("implement me");
	}

	public String visit(VcFieldReference fieldRef) {
		throw new RuntimeException("implement me");
	}

	public String visit(VcFieldStore fieldStore) {
		throw new RuntimeException("implement me");
	}

	public String visit(VcArrayReference arrayRef) {
		throw new RuntimeException("implement me");
	}

	public String visit(VcArrayAllocationExpression vcArrayAllocationExpression) {
		throw new RuntimeException("implement me");
	}

	public String visit(VcAndNary vcAndNary) {
		StringBuffer conjuncts = new StringBuffer();
		for (int i = 0; i < vcAndNary.conjuncts.length; i++) {
			if (i > 0)
				conjuncts.append(" AND "); //$NON-NLS-1$
			conjuncts.append(vcAndNary.conjuncts[i].accept(this));
		}
		return "(" + conjuncts + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
