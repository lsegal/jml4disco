package org.jmlspecs.jml4.esc.provercoordinator.prover.simplify;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;
import org.jmlspecs.jml4.esc.util.Counter;
import org.jmlspecs.jml4.esc.util.Type;
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

public class SimplifyVisitor extends ProverVisitor {

	private static final String BAR = "|"; //$NON-NLS-1$
	private int inLeftOfImplies = 0;
	private Counter counter = new Counter();
	private HashMap/*<String, String>*/ quantifierConstants = new HashMap/*<String, String>*/();
	private boolean inConditional = false;
	private boolean inLeft() {
		return this.inLeftOfImplies > 0;
	}

	public String visit(VcBooleanConstant bool) {
		String label = "(LBLNEG |const@" + bool.sourceStart + "_" + bool.sourceEnd + "| "; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		String trans = "(EQ |@true| |" + (bool.value ? "@true" : "bool$false") + "|) ";    //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$//$NON-NLS-4$
		String result = wrap(bool, label, trans);
		return result;
	}


	public String visitAsTerm(VcBooleanConstant bool) {
		String trans = BAR + (bool.value ? "@true" : "bool$false") + BAR + " ";  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return wrap(bool, trans);
	}

	public String visit(VcIntegerConstant intConst) {
		return wrap(intConst, ""+intConst.value); //$NON-NLS-1$

	}

	public String visit(VcVariable var) {
		String name = var.name + POS_SEP + var.pos + INC_SEP + var.incarnation;
		String label = var.sourceStart==0 ? "" : "(LBLNEG |var@" + var.sourceStart + "_" + var.sourceEnd + "| "; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		String trans = "(EQ |@true| |" + name + "| )"; //$NON-NLS-1$//$NON-NLS-2$
		return wrap(var, label, trans);  
	}

	public String visitAsTerm(VcVariable var) {
		String name = var.name + POS_SEP + var.pos + INC_SEP + var.incarnation;
		return wrap(var, BAR + name + BAR);
	}

	public String visit(VcAnd vcAnd) {
		String left = vcAnd.left.accept(this).trim();
		String right = vcAnd.right.accept(this).trim();
		return wrap(vcAnd, "(AND " + left + " " + right + ")"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	public String visitAsTerm(VcAnd vcAnd) {
		String left = vcAnd.left.acceptAsTerm(this).trim();
		String right = vcAnd.right.acceptAsTerm(this).trim();
		String trans = "(boolAnd " + left + " " + right + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return wrap(vcAnd, trans);
	}

	public String visit(VcLogicalExpression vcExpr) {
		String operator = getOperator(vcExpr.operator, vcExpr.left.type);

		if (vcExpr.operator.equals(VcOperator.IMPLIES)) {
			boolean shouldHandleLhsDifferently = shouldHandleLhsDifferently(vcExpr);
			if (shouldHandleLhsDifferently)
				this.inLeftOfImplies++;
			String left = vcExpr.left.accept(this).trim();
			if (shouldHandleLhsDifferently)
				this.inLeftOfImplies --;
			
			String right = vcExpr.right.accept(this);
			String trans = "("+operator+" " + left + " " + right + ")";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
			return wrap(vcExpr, trans);
		} else {
			String left = vcExpr.left.acceptAsTerm(this);
			String right = vcExpr.right.acceptAsTerm(this);
			String label = "(LBLNEG |eq@" + vcExpr.sourceStart + "_" + vcExpr.sourceEnd + "| "; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			String trans = "(EQ |@true| (" + operator + " " + left.trim() + " " + right + "))"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
			return wrap(vcExpr, label,trans);
		}
	}

	private boolean shouldHandleLhsDifferently(VcLogicalExpression vcExpr) {
		return !vcExpr.hasName() && !(vcExpr.kindOfAssertion() != null && vcExpr.isImplication())
		    && !(vcExpr.left  instanceof VcAndNary)
		    && !(vcExpr.right instanceof VcVariable && ((VcVariable)vcExpr.right).name.equals("start$ok")); //$NON-NLS-1$
	}

	public String visitAsTerm(VcLogicalExpression vcExpr) {
		String operator = getOperator(vcExpr.operator, vcExpr.left.type);
		if (operator.equals("IMPLIES")) //$NON-NLS-1$
			operator = "boolImplies"; //$NON-NLS-1$
		String left = vcExpr.left.acceptAsTerm(this);
		String right = vcExpr.right.acceptAsTerm(this);
		String trans = "(" + operator + " " + left.trim() + " " + right + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		return wrap(vcExpr, trans);
	}

	public String visit(VcOr vcOr) {
		String label = "(LBLNEG |or@" + vcOr.sourceStart + "_" + vcOr.sourceEnd + "| "; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		String left = vcOr.left.accept(this);
		String right = vcOr.right.accept(this);
		String trans = "(OR " + left.trim() + " " + right + ")";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
		return wrap(vcOr, label, trans);
	}

	public String visitAsTerm(VcOr vcOr) {
		String left = vcOr.left.acceptAsTerm(this);
		String right = vcOr.right.acceptAsTerm(this);
		String trans = "(boolOr " + left + " " + right + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		return wrap(vcOr, trans);
	}

	public String visit(VcNot vcNot) {
		String label = "(LBLNEG |not@" + vcNot.sourceStart + "_" + vcNot.sourceEnd + "| ";  //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		String expr = vcNot.vc.accept(this);
		String trans = "(NOT " + expr + " )"; //$NON-NLS-1$ //$NON-NLS-2$
		return wrap(vcNot, label, trans);
	}

	public String visitAsTerm(VcNot vcNot) {
		String expr = vcNot.vc.acceptAsTerm(this);
		String trans = "(boolNot " + expr + " )"; //$NON-NLS-1$ //$NON-NLS-2$
		return wrap(vcNot, trans);
	}

	public String visit(VcRelativeExpression vcRelExpr) {
		String operator = getOperator(vcRelExpr.operator, vcRelExpr.left.type);
		String left = vcRelExpr.left.acceptAsTerm(this);
		String right = vcRelExpr.right.acceptAsTerm(this);
		String label = "(LBLNEG |eq@" + vcRelExpr.sourceStart + "_" + vcRelExpr.sourceEnd + "| "; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		String trans = "(EQ |@true|  (" + operator + " " + left.trim() + " " + right + "))"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		return wrap(vcRelExpr, label, trans);
	}

	public String visitAsTerm(VcRelativeExpression vcRelExpr) {
		String operator = getOperator(vcRelExpr.operator, vcRelExpr.left.type);
		String left = vcRelExpr.left.acceptAsTerm(this);
		String right = vcRelExpr.right.acceptAsTerm(this);
		String trans = "(" + operator + " " + left.trim() + " " + right.trim() + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		return wrap(vcRelExpr, trans);
	}

	public String visit(VcArithExpression vcArithExpr) {
		String operator = getOperator(vcArithExpr.operator, vcArithExpr.left.type);
		String left = vcArithExpr.left.acceptAsTerm(this);
		String right = vcArithExpr.right.acceptAsTerm(this);
		String trans = "(" + operator + " " + left.trim() + " " + right + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		return wrap(vcArithExpr, trans);
	}

	public String visit(VcConditionalExpression condExpr) {
		boolean previousInConditional = this.inConditional;
		this.inConditional = true;
		String cond = condExpr.condition.acceptAsTerm(this);
		String ifTrue = condExpr.valueIfTrue.acceptAsTerm(this);
		String ifFalse = condExpr.valueIfFalse.acceptAsTerm(this);
		this.inConditional = previousInConditional;
		String label = "(LBLNEG |cond@" + condExpr.sourceStart + "_" + condExpr.sourceEnd + "| "; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		String trans = "(EQ |@true| (termConditional " + cond.trim() + " " + ifTrue + " " + ifFalse + " ))"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		return wrap(condExpr, label, trans); 
	}

	public String visitAsTerm(VcConditionalExpression condExpr) {
		String cond = condExpr.condition.acceptAsTerm(this);
		String ifTrue = condExpr.valueIfTrue.acceptAsTerm(this);
		String ifFalse = condExpr.valueIfFalse.acceptAsTerm(this);
		String trans = "(termConditional " + cond.trim() + " " + ifTrue + " " + ifFalse + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		return wrap(condExpr, trans);
	}

	public String visit(VcSuperReference superRef) {
		return "this"; //$NON-NLS-1$
	}

	public String visit(VcThisReference thisRef) {
		return "this"; //$NON-NLS-1$
	}

	public String visit(VcFieldReference fieldRef) {
		String receiver = fieldRef.receiver.acceptAsTerm(this);
		String trans = "(select |"+fieldRef.field+"$"+fieldRef.incarnation+"| "+receiver+")"; //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$ //$NON-NLS-4$
		return trans;
	}

	public String visit(VcFieldStore fieldStore) {
		String receiver = fieldStore.field.receiver.acceptAsTerm(this);
		String value    = fieldStore.value.acceptAsTerm(this);
		String trans = "(EQ |"+  //$NON-NLS-1$
			fieldStore.field.field+"$"+fieldStore.newIncarnation+"| "+ //$NON-NLS-1$ //$NON-NLS-2$
			"(store |"+fieldStore.field.field+"$"+fieldStore.oldIncarnation+"| "+ //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		          	  receiver+" "+value+"))"; //$NON-NLS-1$ //$NON-NLS-2$
		return wrap(fieldStore, trans);
	}

	public String visit(VcArrayReference arrayRef) {
		String receiver = arrayRef.receiver.acceptAsTerm(this);
		String position = arrayRef.position.acceptAsTerm(this);
		String trans = "(select (select |elems<"+arrayRef.incarnation+">| "+receiver+") "+position+")"; //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$ //$NON-NLS-4$
		return trans;
	}

	public String visit(VcArrayAllocationExpression vcArrayAllocationExpression) {
		return "something_meaningful";
	}

	public String visit(VcQuantifiedExpression expr) {
		String op = getQuantifier(expr.quantifier);
		String joiner = op.equals("FORALL") ? "IMPLIES" : "AND";   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
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
		String trans = "(" + op + " (" + vars + ") (" + joiner + " " + range + " " + body + "))"; //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$//$NON-NLS-4$ //$NON-NLS-5$ //$NON-NLS-6$
		String label = "(LBLNEG |cond@" + expr.sourceStart + "_" + expr.sourceEnd + "| "; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$

		if (this.inConditional) {
			String replacement = (String) this.quantifierConstants.get(trans);
			if (replacement == null) {
				replacement = op + INC_SEP + this.counter.getAndIncCounter();
				this.quantifierConstants.put(trans, replacement);
			}
			trans = BAR + replacement + BAR;
		}
		
		return wrap(expr, label, trans);
	}

	public String visitAsTerm(VcQuantifiedExpression expr) {
		String op = getQuantifier(expr.quantifier);
		String trans;
		if (expr.quantifier.isLogical()) {
			String joiner = op.equals("FORALL") ? "IMPLIES" : "AND";   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
			String range = expr.range.accept(this);
			String body = expr.body.accept(this);
			String vars = translateBoundVars(expr.range.decls());
			trans = "(" + op + " (" + vars + ") (" + joiner + " " + range + " " + body + "))";    //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$//$NON-NLS-4$ //$NON-NLS-5$ //$NON-NLS-6$
	
			if (true || this.inConditional) {
				String replacement = (String) this.quantifierConstants.get(trans);
				if (replacement == null) {
					replacement = getReplacementForQuantifiedExpression(op);
					this.quantifierConstants.put(trans, replacement);
				}
				trans = BAR + replacement + BAR;
			}
		} else {
			Utils.assertTrue(expr.quantifier.isNumeric(), "expecting a numeric quantifier but was '"+op+"'");  //$NON-NLS-1$//$NON-NLS-2$
			trans = BAR + getReplacementForQuantifiedExpression(op) + BAR;
		}
		
		return trans;
	}

	private String getReplacementForQuantifiedExpression(String op) {
		return (op + INC_SEP + this.counter.getAndIncCounter()).toLowerCase();
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
		Utils.assertTrue(false, quantifier.lexeme + " not yet implemented"); //$NON-NLS-1$
		return null;
	}

	private String translateBoundVars(List varDecls) {
		StringBuffer result = new StringBuffer();
		boolean firstTime = true;
		for (Iterator iterator = varDecls.iterator(); iterator.hasNext();) {
			VcVarDecl var = (VcVarDecl) iterator.next();
			String name = BAR + var.name + '@' + var.pos + ZERO_INCARNATION + BAR;
			if (firstTime) {
				firstTime = false;
			} else {
				result.append(" "); //$NON-NLS-1$
			}
			result.append(name);
		}
		return result.toString();
	}

	public String visit(VcVarDecl vcVarDecl, int max) {
		String simplifyType = getType(vcVarDecl);
		StringBuffer result = new StringBuffer();
		for (int i=0; i <= max; i++) {
			String trans = "(EQ |@true| (is |" + vcVarDecl.name + "@" + i + "| " + simplifyType+"))"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
			String varDecl = wrap(vcVarDecl, trans);
			result.append(varDecl);
		}
		return result.toString();
	}

	private String getType(VcVarDecl vcVarDecl) {
		String mappedType = (String) typesMap.get(vcVarDecl.type);
		String simplifyType = mappedType == null ? vcVarDecl.type.debugName() : mappedType;
		return simplifyType;
	}

	private String getOperator(VcOperator operator, TypeBinding operandType) {
		if (operator.equals(VcOperator.EQUALS)) {
			if (operandType.equals(TypeBinding.BOOLEAN)) {
				return "boolEq"; //$NON-NLS-1$
			} else {
				return "integralEQ"; //$NON-NLS-1$
			}
		}
		if (operator.equals(VcOperator.NOT_EQUALS)) {
			if (operandType.equals(TypeBinding.BOOLEAN)) {
				return "boolNe"; //$NON-NLS-1$
			} else {
				return "integralNE"; //$NON-NLS-1$
			}
		}
		if (operator.equals(VcOperator.LESS)) {
			if (Type.isIntegral(operandType)) {
				return "integralLT"; //$NON-NLS-1$
			}
		}
		if (operator.equals(VcOperator.LESS_EQUALS)) {
			if (Type.isIntegral(operandType)) {
				return "integralLE"; //$NON-NLS-1$
			}
		}
		if (operator.equals(VcOperator.GREATER)) {
			if (Type.isIntegral(operandType)) {
				return "integralGT"; //$NON-NLS-1$
			}
		}
		if (operator.equals(VcOperator.GREATER_EQUALS)) {
			if (Type.isIntegral(operandType)) {
				return "integralGE"; //$NON-NLS-1$
			}
		}
		if (operator.equals(VcOperator.PLUS)) {
			if (Type.isIntegral(operandType)) {
				return "+"; //$NON-NLS-1$
			}
		}
		if (operator.equals(VcOperator.MINUS)) {
			if (Type.isIntegral(operandType)) {
				return "-"; //$NON-NLS-1$
			}
		}
		if (operator.equals(VcOperator.TIMES)) {
			if (Type.isIntegral(operandType)) {
				return "*"; //$NON-NLS-1$
			}
		}
		if (operator.equals(VcOperator.DIVIDE)) {
			if (Type.isIntegral(operandType)) {
				return "integralDiv"; //$NON-NLS-1$
			}
		}
	    if (operator.equals(VcOperator.REMAINDER)) {
			if (Type.isIntegral(operandType)) {
				return "integralMod"; //$NON-NLS-1$
			}
		}
	    if (operator.equals(VcOperator.IMPLIES)) {
			if (Type.isBoolean(operandType)) {
				return "IMPLIES"; //$NON-NLS-1$
			}
		}
	    if (operator.equals(VcOperator.EQUIV)) {
			if (Type.isBoolean(operandType)) {
				return "boolEq"; //$NON-NLS-1$
			}
		}
	    if (operator.equals(VcOperator.NOT_EQUIV)) {
			if (Type.isBoolean(operandType)) {
				return "boolNE"; //$NON-NLS-1$
			}
		}
	    throw new RuntimeException("operator not translated properly ("+operator + "::" +operandType.debugName()+")"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

	private static final Map typesMap = new HashMap();
	static {
		typesMap.put(TypeBinding.BOOLEAN, "T_boolean"); //$NON-NLS-1$ 
		typesMap.put(TypeBinding.BYTE,    "T_byte"); //$NON-NLS-1$
		typesMap.put(TypeBinding.CHAR,    "T_char"); //$NON-NLS-1$
		typesMap.put(TypeBinding.SHORT,   "T_short"); //$NON-NLS-1$
		typesMap.put(TypeBinding.INT,     "T_int"); //$NON-NLS-1$
		typesMap.put(TypeBinding.LONG,    "T_long"); //$NON-NLS-1$
		typesMap.put(TypeBinding.FLOAT,   "T_float"); //$NON-NLS-1$
		typesMap.put(TypeBinding.DOUBLE,  "T_double"); //$NON-NLS-1$
	}

	private String wrap(VC vc, String vcTrans) {
		return wrap(vc, "", vcTrans); //$NON-NLS-1$
	}

	private String wrap(VC vc, String label, String vcTrans) {
		Utils.assertTrue(count(vcTrans, '(') == count(vcTrans, ')'), "parens don't match"); //$NON-NLS-1$
		int kindOfLabel = vc.kindOfLabel();
		boolean shouldIgnoreLabel = shouldIgnoreLabel(vc, kindOfLabel);
	    String preLabel = preLabel(vc, kindOfLabel, shouldIgnoreLabel);
		String postLabel = postLabel(vc, kindOfLabel, shouldIgnoreLabel);
		String result = preLabel +
  		       			label +
  		       			vcTrans +
  		       			(label.length() == 0 ? "" : ")") +  //$NON-NLS-1$//$NON-NLS-2$
  		       			postLabel;
		Utils.assertTrue(count(result, '(') == count(result, ')'), "parens don't match"); //$NON-NLS-1$
		return result.trim();
	}

	private int count(String s, char c) {
		char[] cs = s.toCharArray();
		int result = 0;
		for (int i = 0; i < cs.length; i++) {
			if (cs[i] == c)
				result++;
		}
		return result;
	}

	private boolean shouldIgnoreLabel(VC vc, int kindOfLabel) {
		return inLeft() || kindOfLabel == VC.NO_LBL || vc.sourceStart <= 0;
	}

	private String preLabel(VC vc, int kindOfLabel, boolean shouldIgnoreLabel) {
		return shouldIgnoreLabel
		     ? "" //$NON-NLS-1$
			 : "(" + kindToString(kindOfLabel) + //$NON-NLS-1$
			   " " + BAR + labelText(vc) + BAR + " "; //$NON-NLS-1$ //$NON-NLS-2$
	}

	private String postLabel(VC vc, int kindOfLabel, boolean shouldIgnoreLabel) {
		return shouldIgnoreLabel
		     ? "" //$NON-NLS-1$
			 : ")"; //$NON-NLS-1$
	}

	private String kindToString(int kindOfLabel) {
		return (kindOfLabel == VC.NEGLBL) ? "LBLNEG" //$NON-NLS-1$
				: "NO_LBL"; //$NON-NLS-1$
	}

	private String labelText(VC vc) {
		if ((vc.kindOfAssertion().equals(KindOfAssertion.LOOP_INVAR) && vc.labelStart() == 0)
		 || (vc.kindOfAssertion().equals(KindOfAssertion.PRE) && vc.labelStart() == 0))
			Utils.assertTrue(false, "here"); //$NON-NLS-1$
		return  vc.kindOfAssertion().description + "@" + vc.labelStart(); //$NON-NLS-1$
	}

	public String getTheory(VC vc, Map incarnations) {
		String result = vc.accept(this);
		return result;
	}

	public String visit(VcAndNary vcAndNary) {
		StringBuffer conjuncts = new StringBuffer();
		for (int i = 0; i < vcAndNary.conjuncts.length; i++) {
			if (i > 0)
				conjuncts.append("\n\t"); //$NON-NLS-1$
			conjuncts.append(vcAndNary.conjuncts[i].accept(this).trim());
		}
		return wrap(vcAndNary, "(AND " + conjuncts.toString() + ")"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}
}
