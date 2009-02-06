package org.jmlspecs.jml4.esc.gc;

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

public interface SugaredExpressionVisitor {
	SugaredExpression visit(SugaredAssignment expr);
	SugaredExpression visit(SugaredBinaryExpression expr);
	SugaredExpression visit(SugaredBooleanConstant expr);
	SugaredExpression visit(SugaredConditionalExpression expr);
	SugaredExpression visit(SugaredIntegerConstant expr);
	SugaredExpression visit(SugaredNotExpression expr);
	SugaredExpression visit(SugaredPostfixExpression expr);
	SugaredExpression visit(SugaredVariable expr);
	SugaredExpression visit(SugaredQuantifiedExpression expr);
	SugaredExpression visit(SugaredOldExpression expr);
	SugaredExpression visit(SugaredMessageSend msgSend);
	SugaredExpression visit(SugaredFieldReference fieldRef);
	SugaredExpression visit(SugaredSuperReference superRef);
	SugaredExpression visit(SugaredThisReference thisRef);
	SugaredExpression visit(SugaredArrayReference arrayRef);
	SugaredExpression visit(SugaredArrayAllocationExpression arrayAlloc);
}
