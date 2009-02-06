package org.jmlspecs.jml4.esc.gc;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredArrayAllocationExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredArrayReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredAssignment;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBinaryExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredBooleanConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredConditionalExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredFieldReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredIntegerConstant;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredMessageSend;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredNotExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredOldExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredPostfixExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredQuantifiedExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredSuperReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredThisReference;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredVariable;
import org.jmlspecs.jml4.esc.util.Utils;

public class VarToOldVisitor implements SugaredExpressionVisitor {

	public VarToOldVisitor() {
		/*empty*/
	}

	public SugaredExpression visit(SugaredAssignment expr) {
		Utils.assertTrue(false, "shouldn't be called on pure expressions"); //$NON-NLS-1$
		return null;
	}

	public SugaredExpression visit(SugaredBinaryExpression expr) {
		SugaredExpression left  = expr.left.accept(this);
		SugaredExpression right = expr.right.accept(this);
		return new SugaredBinaryExpression(expr.operator, left, right, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public SugaredExpression visit(SugaredBooleanConstant expr) {
		return expr;
	}

	public SugaredExpression visit(SugaredConditionalExpression expr) {
		SugaredExpression cond    = expr.condition.accept(this);
		SugaredExpression ifTrue  = expr.valueIfTrue.accept(this);
		SugaredExpression ifFalse = expr.valueIfFalse.accept(this);
		return new SugaredConditionalExpression(cond, ifTrue, ifFalse, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public SugaredExpression visit(SugaredIntegerConstant expr) {
		return expr;
	}

	public SugaredExpression visit(SugaredNotExpression notExpr) {
		SugaredExpression expr = notExpr.expr.accept(this);
		return new SugaredNotExpression(expr, notExpr.sourceStart, notExpr.sourceEnd);
	}

	public SugaredExpression visit(SugaredPostfixExpression expr) {
		Utils.assertTrue(false, "shouldn't be called on pure expressions"); //$NON-NLS-1$
		return null;
	}

	public SugaredExpression visit(SugaredVariable expr) {
		return expr.isStaticField
		     ? (SugaredExpression) expr
		     : new SugaredOldExpression(expr, expr.sourceStart, expr.sourceEnd);
	}

	public SugaredExpression visit(SugaredQuantifiedExpression expr) {
		SugaredExpression range = expr.range.accept(this);
		SugaredExpression body = expr.body.accept(this);
		return new SugaredQuantifiedExpression(expr.quantifier, range, body, expr.boundVariables, expr.type, expr.sourceStart, expr.sourceEnd);
	}

	public SugaredExpression visit(SugaredOldExpression expr) {
		return expr;
	}

	public SugaredExpression visit(SugaredMessageSend sugaredMessageSend) {
		SugaredExpression receiver = sugaredMessageSend.receiver.accept(this);
		String selector = sugaredMessageSend.selector;
		TypeBinding type = sugaredMessageSend.type;
		SugaredVarDecl[] formalParams = sugaredMessageSend.formalParams;
		SugaredExpression[] actualParams = new SugaredExpression[sugaredMessageSend.actualParams.length];
		for (int i = 0; i < actualParams.length; i++) {
			actualParams[i] = sugaredMessageSend.actualParams[i].accept(this);
		}
		SugaredExpression pre = sugaredMessageSend.pre.accept(this);
		SugaredExpression post = sugaredMessageSend.post.accept(this);
		int count = sugaredMessageSend.countForLabels;
		return new SugaredMessageSend(count, receiver, selector, formalParams, actualParams, type, pre, post, sugaredMessageSend.sourceStart, sugaredMessageSend.sourceEnd);
	}

	public SugaredExpression visit(SugaredFieldReference fieldRef) {
		SugaredExpression receiver = fieldRef.receiver.accept(this);
		return receiver == fieldRef.receiver
		     ? fieldRef
		     : new SugaredFieldReference(receiver, fieldRef.field, fieldRef.declaringClass, fieldRef.type, fieldRef.sourceStart, fieldRef.sourceEnd);
	}

	public SugaredExpression visit(SugaredSuperReference superRef) {
		return superRef;
	}

	public SugaredExpression visit(SugaredThisReference thisRef) {
		return thisRef;
	}

	public SugaredExpression visit(SugaredArrayReference arrayRef) {
		SugaredExpression receiver = arrayRef.receiver.accept(this);
		SugaredExpression position = arrayRef.position.accept(this);
		return receiver == arrayRef.receiver && position == arrayRef.position
		     ? arrayRef
		     : new SugaredArrayReference(receiver, position, arrayRef.type, arrayRef.sourceStart, arrayRef.sourceEnd);
	}

	public SugaredExpression visit(SugaredArrayAllocationExpression arrayAlloc) {
		Utils.assertTrue(false, "shouldn't be called on pure expressions"); //$NON-NLS-1$
		return null;
	}

}
