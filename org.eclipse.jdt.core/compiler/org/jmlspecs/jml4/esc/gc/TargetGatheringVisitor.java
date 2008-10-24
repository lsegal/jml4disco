package org.jmlspecs.jml4.esc.gc;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssert;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredAssume;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBlock;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredBreakStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredContinueStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredExprStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredGoto;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredHavoc;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredIfStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPostcondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredPrecondition;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredProgram;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredReturnStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredSequence;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredWhileStatement;
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

public class TargetGatheringVisitor implements SimplifyingVisitor, SugaredExpressionVisitor {

	private final List/*<SugaredExpression>*/ targets = new ArrayList/*<SugaredExpression>*/();

	public TargetGatheringVisitor() {
		/*empty*/
	}

	public SugaredExpression[] getResult() {
		return (SugaredExpression[])this.targets.toArray(new SugaredExpression[0]);
	}

	public SugaredProgram visit(SugaredProgram sugaredProgram) {
		throw new RuntimeException("shouldn't be called"); //$NON-NLS-1$
	}

	public SugaredBlock[] visit(SugaredBlock sugaredBlock) {
		throw new RuntimeException("shouldn't be called"); //$NON-NLS-1$
	}

	public SugaredStatement visit(SugaredSequence sugaredSequence) {
		sugaredSequence.stmt1.accept(this);
		sugaredSequence.stmt2().accept(this);
		return null;
	}

	public SugaredStatement visit(SugaredAssert sugaredAssert) {
		sugaredAssert.pred.accept(this);
		return null;
	}

	public SugaredStatement visit(SugaredAssume sugaredAssume) {
		sugaredAssume.pred.accept(this);
		return null;
	}

	public SugaredStatement visit(SugaredIfStatement sugaredIfStatement) {
		sugaredIfStatement.condition.accept(this);
		sugaredIfStatement.thenStatement.accept(this);
		sugaredIfStatement.elseStatement.accept(this);
		return null;
	}

	public String toString() {
		return "[TargetGatheringVisitor: "+this.targets+"]";  //$NON-NLS-1$//$NON-NLS-2$
	}

	public SugaredStatement visit(SugaredWhileStatement sugaredWhileStatement) {
		sugaredWhileStatement.condition.accept(this);
		sugaredWhileStatement.action.accept(this);
		return null;
	}

	public SugaredStatement visit(SugaredVarDecl sugaredVarDecl) {
		return null;
	}

	public SugaredStatement visit(SugaredGoto sugaredGoto) {
		return null;
	}

	public SugaredStatement visit(SugaredBreakStatement sugaredBreakStatement) {
		return null;
	}

	public SugaredStatement visit(SugaredContinueStatement sugaredContinueStatement) {
		return null;
	}

	public SugaredStatement visit(SugaredReturnStatement sugaredReturnStatement) {
		if (sugaredReturnStatement.expr != null)
			sugaredReturnStatement.expr.accept(this);
		return null;
	}

	public SugaredStatement visit(SugaredExprStatement sugaredExprStatement) {
		sugaredExprStatement.expr.accept(this);
		return null;
	}

	public SugaredExpression visit(SugaredAssignment expr) {
		this.targets.add(expr.lhs);
		expr.expr.accept(this);
		return null;
	}

	public SugaredExpression visit(SugaredBinaryExpression expr) {
		expr.left.accept(this);
		expr.right.accept(this);
		return null;
	}

	public SugaredExpression visit(SugaredBooleanConstant expr) {
		return null;
	}

	public SugaredExpression visit(SugaredConditionalExpression expr) {
		expr.condition.accept(this);
		expr.valueIfTrue.accept(this);
		expr.valueIfFalse.accept(this);
		return null;
	}

	public SugaredExpression visit(SugaredIntegerConstant expr) {
		return null;
	}

	public SugaredExpression visit(SugaredNotExpression expr) {
		expr.expr.accept(this);
		return null;
	}

	public SugaredExpression visit(SugaredPostfixExpression expr) {
		this.targets.add(expr.lhs);
		return null;
	}

	public SugaredExpression visit(SugaredVariable expr) {
		return null;
	}

	public SugaredStatement visit(SugaredHavoc sugaredHavoc) {
		this.targets.add(sugaredHavoc.var);
		return null;
	}

	public SugaredExpression visit(SugaredQuantifiedExpression expr) {
		return null;
	}

	public SugaredStatement visit(SugaredPrecondition sugaredPrecondition) {
		throw new RuntimeException("shouldn't be called"); //$NON-NLS-1$
	}

	public SugaredStatement visit(SugaredPostcondition sugaredPostcondition) {
		throw new RuntimeException("shouldn't be called"); //$NON-NLS-1$
	}

	public SugaredExpression visit(SugaredOldExpression expr) {
		return null;
	}

	public SugaredExpression visit(SugaredMessageSend sugaredMessageSend) {
		return null;
	}

	public SugaredExpression visit(SugaredFieldReference fieldRef) {
		fieldRef.receiver.accept(this);
		return null;
	}

	public SugaredExpression visit(SugaredSuperReference superRef) {
		return null;
	}

	public SugaredExpression visit(SugaredThisReference thisRef) {
		return null;
	}

	public SugaredExpression visit(SugaredArrayReference arrayRef) {
		arrayRef.receiver.accept(this);
		arrayRef.position.accept(this);
		return null;
	}

	public SugaredExpression visit(SugaredArrayAllocationExpression arrayAlloc) {
		//FIXME: does anything need to go here?
		//       like checking dims, inits etc?
		return null;
	}
}
