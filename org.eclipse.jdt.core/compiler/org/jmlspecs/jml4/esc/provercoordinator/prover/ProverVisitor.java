package org.jmlspecs.jml4.esc.provercoordinator.prover;

import java.util.Map;

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
import org.jmlspecs.jml4.esc.vc.lang.VcOr;
import org.jmlspecs.jml4.esc.vc.lang.VcQuantifiedExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcRelativeExpression;
import org.jmlspecs.jml4.esc.vc.lang.VcSuperReference;
import org.jmlspecs.jml4.esc.vc.lang.VcThisReference;
import org.jmlspecs.jml4.esc.vc.lang.VcVarDecl;
import org.jmlspecs.jml4.esc.vc.lang.VcVariable;


public abstract class ProverVisitor {

	protected static final String ZERO_INCARNATION = "$0"; //$NON-NLS-1$
	protected static final char POS_SEP = '@';
	protected static final char INC_SEP = '$';

	public abstract String visit(VcVariable vcVar);
	public abstract String visit(VcAnd vcAnd);
	public abstract String visit(VcLogicalExpression vcImplies);
	public abstract String visit(VcOr vcOr);
	public abstract String visit(VcNot vcNot);
	public abstract String visit(VcVarDecl vcVarDecl, int max);
	public abstract String visit(VcConditionalExpression vcCond);
	public abstract String visit(VcBooleanConstant vcBool);
	public abstract String visit(VcIntegerConstant vcInt);
	public abstract String visit(VcRelativeExpression vcEq);
	public abstract String visit(VcArithExpression vcArithExpr);
	public abstract String visitAsTerm(VcBooleanConstant vcBool);
	public abstract String visitAsTerm(VcConditionalExpression vcCond);
	public abstract String visitAsTerm(VcRelativeExpression vcRelExpr);
	public abstract String visitAsTerm(VcAnd vcAnd);
	public abstract String visitAsTerm(VcLogicalExpression vcImplies);
	public abstract String visitAsTerm(VcOr vcOr);
	public abstract String visitAsTerm(VcNot vcNot);
	public abstract String visitAsTerm(VcVariable vcVar);
	public abstract String visit(VcQuantifiedExpression expr);
	public abstract String visitAsTerm(VcQuantifiedExpression expr);
	public abstract String visit(VcSuperReference superRef);
	public abstract String visit(VcThisReference thisRef);
	public abstract String visit(VcFieldReference fieldRef);
	public abstract String visit(VcFieldStore fieldStore);
	public abstract String visit(VcArrayReference arrayRef);
	public abstract String visit(VcArrayAllocationExpression vcArrayAllocationExpression);
	public abstract String visit(VcAndNary vcAndNary);

	public String getVarDecls(VC[] vcs, Map/* <String var, Integer> */incarnations) {
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < vcs.length; i++) {
			VcVarDecl[] decls = (VcVarDecl[])vcs[i].decls().toArray(new VcVarDecl[0]);
			for (int j = 0; j < decls.length; j++) {
				VcVarDecl varDecl = decls[j];

				Integer fromMap = (Integer) incarnations.get(varDecl.name);
				int max = (fromMap == null ? 0 : fromMap.intValue());
				result.append(varDecl.accept(this, max));
			}
		}
		return result.toString();
	}
}
