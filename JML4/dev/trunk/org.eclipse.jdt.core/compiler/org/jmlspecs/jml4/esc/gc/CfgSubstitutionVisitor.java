package org.jmlspecs.jml4.esc.gc;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgAssert;
import org.jmlspecs.jml4.esc.gc.lang.CfgAssume;
import org.jmlspecs.jml4.esc.gc.lang.CfgSequence;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;
import org.jmlspecs.jml4.esc.gc.lang.CfgVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgArrayAllocationExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgArrayReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgConditionalExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgFieldReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgFieldStore;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgOperator;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgSuperReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgThisReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgVariable;
import org.jmlspecs.jml4.esc.util.Utils;

public class CfgSubstitutionVisitor implements CfgExpressionVisitor {

	public Map/*<CfgVariable, CfgExpression>*/ map = new HashMap/*<CfgVariable, CfgExpression>*/();

	public CfgSubstitutionVisitor(List/*<CfgStatement>*/ bindings) {
		for (Iterator iterator = bindings.iterator(); iterator.hasNext();) {
			CfgStatement stmt = (CfgStatement) iterator.next();
			Utils.assertTrue(stmt instanceof CfgAssume || stmt instanceof CfgSequence, "stmt isn't a CfgAssume but a '"+stmt.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
			addMapEntries(stmt);
		}
	}

	public CfgSubstitutionVisitor(Map map) {
		this.map = map;
	}

	private void addMapEntries(CfgStatement stmt) {
		if (stmt instanceof CfgSequence) {
		   CfgStatement stmt1 = ((CfgSequence)stmt).stmt1;
		   CfgStatement stmt2 = ((CfgSequence)stmt).stmt2;
		   addMapEntries(stmt1);
		   addMapEntries(stmt2);
		} else if (stmt instanceof CfgAssume) {
			CfgExpression init = ((CfgAssume) stmt).pred;
			if (init instanceof CfgBinaryExpression) {
				CfgBinaryExpression eq = (CfgBinaryExpression) init;
				if (eq.operator == CfgOperator.EQUALS) {
					CfgExpression left = eq.left;
					CfgExpression right = eq.right;
					CfgExpression oldRight;
					do {
						oldRight = right;
					    right = right.accept(this);
					} while (right != oldRight);
					if (left instanceof CfgVariable) {
						CfgVariable var = (CfgVariable)left;
						String key = var.name + "$" + var.pos; //$NON-NLS-1$
						map.put(key, right);
					}
				}
			}
		} else {
			Utils.assertTrue(stmt instanceof CfgVarDecl
					      || stmt instanceof CfgAssert, "stmt isn't an assert but a '"+stmt.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
		}
	}

	public String toString() {
		return "CfgSubstitutionVisitor: "+this.map.toString(); //$NON-NLS-1$
	}

	public CfgExpression visit(CfgVariable var) {
		String key = var.name + "$" + var.pos; //$NON-NLS-1$
		CfgExpression right = (CfgExpression) map.get(key);
		return (right == null)
		     ? var
		     : right;
	}

	public CfgExpression visit(CfgBooleanConstant bool) {
		return bool;
	}

	public CfgExpression visit(CfgIntegerConstant intConst) {
		return intConst;
	}

	public CfgExpression visit(CfgNotExpression cfgNotExpression) {
		CfgExpression expr = cfgNotExpression.expr.accept(this);
		return (expr == cfgNotExpression.expr)
			 ? cfgNotExpression
		     : new CfgNotExpression(expr, cfgNotExpression.sourceStart, cfgNotExpression.sourceEnd);
	}

	public CfgExpression visit(CfgBinaryExpression binExpr) {
		boolean isVarInit = (binExpr.left instanceof CfgVariable) && binExpr.operator == CfgOperator.EQUALS;
		CfgExpression left = isVarInit
		                   ? binExpr.left // don't substitute lhs of ==
		                   : binExpr.left.accept(this);
		CfgExpression right = binExpr.right.accept(this);
		if (isVarInit) {
			String key = ((CfgVariable)left).name + "$" + ((CfgVariable)left).pos; //$NON-NLS-1$
			if (this.map.get(key) == null) {
				this.map.put(key, right);
			}
		}
		return (left == binExpr.left && right == binExpr.right)
			 ? binExpr
		     : new CfgBinaryExpression(binExpr.operator, left, right, binExpr.type, binExpr.sourceStart, binExpr.sourceEnd);
	}

	public CfgExpression visit(CfgConditionalExpression condExpr) {
		CfgExpression cond = condExpr.condition.accept(this);
		CfgExpression ifTrue = condExpr.valueIfTrue.accept(this);
		CfgExpression ifFalse = condExpr.valueIfFalse.accept(this);
		return (cond == condExpr.condition && ifTrue == condExpr.valueIfTrue && ifFalse == condExpr.valueIfFalse)
			 ? condExpr
		     : new CfgConditionalExpression(cond, ifTrue, ifFalse, condExpr.type, condExpr.sourceStart, condExpr.sourceEnd);
	}

	public CfgExpression visit(CfgQuantifiedExpression expr) {
		CfgExpression range = expr.range.accept(this);
		CfgExpression body = expr.body.accept(this);
		return (range == expr.range && body == expr.body)
			 ? expr
		     : new CfgQuantifiedExpression(expr.quantifier, range, body, expr.boundVariables, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public CfgExpression visit(CfgSuperReference superRef) {
		return superRef;
	}

	public CfgExpression visit(CfgThisReference thisRef) {
		return thisRef;
	}

	public CfgExpression visit(CfgFieldReference fieldRef) {
		return fieldRef;
	}

	public CfgExpression visit(CfgFieldStore fieldStore) {
		CfgExpression value = fieldStore.value.accept(this);
		return value == fieldStore.value
		     ? fieldStore
		     : new CfgFieldStore(fieldStore.field, fieldStore.sourceStart, fieldStore.sourceEnd, value);
	}

	public CfgExpression visit(CfgArrayReference arrayRef) {
		CfgExpression receiver = arrayRef.receiver.accept(this);
		CfgExpression position = arrayRef.position.accept(this);
		return receiver == arrayRef.receiver && position == arrayRef.position
		     ? arrayRef
		     : new CfgArrayReference(receiver, position, arrayRef.incarnation(), arrayRef.type, arrayRef.sourceStart, arrayRef.sourceEnd);
	}

	public CfgExpression visit(CfgArrayAllocationExpression arrayAlloc) {
		return arrayAlloc;
	}

	public CfgStatement visit(CfgStatement stmt) {
		if (stmt instanceof CfgSequence) {
		   CfgStatement stmt1 = visit(((CfgSequence)stmt).stmt1);
		   CfgStatement stmt2 = visit(((CfgSequence)stmt).stmt2);
		   return new CfgSequence(stmt1, stmt2);
		} else if (stmt instanceof CfgAssume) {
			CfgExpression pred = ((CfgAssume) stmt).pred.accept(this);
			return new CfgAssume(pred, stmt.sourceStart);
		} else {
			Utils.assertTrue(stmt instanceof CfgAssert, "stmt isn't an assert but a '"+stmt.getClass().getName()+"'"); //$NON-NLS-1$ //$NON-NLS-2$
			CfgExpression pred = ((CfgAssert) stmt).pred;
			return new CfgAssert(pred, ((CfgAssert) stmt).kind, stmt.sourceStart);
		}
	}

}
