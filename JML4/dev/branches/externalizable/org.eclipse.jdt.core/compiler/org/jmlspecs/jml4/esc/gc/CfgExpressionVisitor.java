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

public interface CfgExpressionVisitor {

	CfgExpression visit(CfgVariable var);
	CfgExpression visit(CfgBooleanConstant bool);
	CfgExpression visit(CfgIntegerConstant intConst);
	CfgExpression visit(CfgNotExpression notExpr);
	CfgExpression visit(CfgBinaryExpression binExpr);
	CfgExpression visit(CfgConditionalExpression condExpr);
	CfgExpression visit(CfgQuantifiedExpression expr);
	CfgExpression visit(CfgSuperReference superRef);
	CfgExpression visit(CfgThisReference thisRef);
	CfgExpression visit(CfgFieldReference fieldRef);
	CfgExpression visit(CfgFieldStore fieldStore);
	CfgExpression visit(CfgArrayReference arrayRef);
	CfgExpression visit(CfgArrayAllocationExpression arrayAlloc);

}