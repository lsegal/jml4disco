package org.jmlspecs.jml4.esc.gc;

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
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgSuperReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgThisReference;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgVariable;
import org.jmlspecs.jml4.esc.util.Utils;

public class ZeroIncarnationVisitor implements CfgExpressionVisitor {

	public CfgExpression visit(CfgVariable var) {
		CfgVariable result = new CfgVariable(var.name, var.pos, var.type, 0, var.sourceStart, var.sourceEnd, var.isStaticField);
		return result;
	}

	public CfgExpression visit(CfgBooleanConstant bool) {
		return bool;
	}

	public CfgExpression visit(CfgIntegerConstant intConst) {
		return intConst;
	}

	public CfgExpression visit(CfgNotExpression cfgNotExpression) {
		CfgExpression expr = cfgNotExpression.expr.accept(this);
		CfgExpression result = new CfgNotExpression(expr, cfgNotExpression.sourceStart, cfgNotExpression.sourceEnd);
		return result;
	}

	public CfgExpression visit(CfgBinaryExpression binExpr) {
		CfgExpression left  = binExpr.left.accept(this);
		CfgExpression right = binExpr.right.accept(this);
		CfgExpression result = new CfgBinaryExpression(binExpr.operator, left, right, binExpr.type, binExpr.sourceStart, binExpr.sourceEnd);
		return result;
	}

	public CfgExpression visit(CfgConditionalExpression condExpr) {
		CfgExpression cond    = condExpr.condition.accept(this);
		CfgExpression ifTrue  = condExpr.valueIfTrue.accept(this);
		CfgExpression ifFalse = condExpr.valueIfFalse.accept(this);
		CfgExpression result = new CfgConditionalExpression(cond, ifTrue, ifFalse, condExpr.type, condExpr.sourceStart, condExpr.sourceEnd);
		return result;
	}

	public CfgExpression visit(CfgQuantifiedExpression expr) {
		CfgExpression body  = expr.body.accept(this);
		CfgExpression range = expr.range.accept(this);
		CfgExpression result = new CfgQuantifiedExpression(expr.quantifier, range, body, expr.boundVariables, expr.type, expr.sourceStart, expr.sourceEnd);
		return result;
	}

	public CfgExpression visit(CfgSuperReference superRef) {
		return superRef;
	}

	public CfgExpression visit(CfgThisReference thisRef) {
		return thisRef;
	}

	public CfgExpression visit(CfgFieldReference fieldRef) {
		CfgExpression receiver = fieldRef.receiver.accept(this);
		CfgFieldReference result = new CfgFieldReference(receiver, fieldRef.field, 0, fieldRef.type, fieldRef.sourceStart, fieldRef.sourceEnd);
		return result;
	}

	public CfgExpression visit(CfgFieldStore fieldStore) {
		Utils.assertTrue(false, "there should be no assignments in postconditions"); //$NON-NLS-1$
		return null;
	}

	public CfgExpression visit(CfgArrayReference arrayRef) {
		CfgExpression receiver = arrayRef.receiver.accept(this);
		CfgExpression position = arrayRef.position.accept(this);
		CfgArrayReference result = new CfgArrayReference(receiver, position, 0, arrayRef.type, arrayRef.sourceStart, arrayRef.sourceEnd);
		return result;
	}

	public CfgExpression visit(CfgArrayAllocationExpression arrayAlloc) {
		Utils.assertTrue(false, "there should be no assignments in postconditions"); //$NON-NLS-1$
		return null;
	}

}
