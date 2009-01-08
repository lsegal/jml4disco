package org.jmlspecs.jml4.esc.gc.lang.expr;

import java.util.Arrays;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.CfgExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgVarDecl;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgQuantifiedExpression extends CfgExpression {

	public final CfgQuantifier quantifier;
	public final CfgExpression range;
	public final CfgExpression body;
	public final CfgVarDecl[] boundVariables;

	public CfgQuantifiedExpression(CfgQuantifier quantifier, CfgExpression range, 
			CfgExpression body, CfgVarDecl[] boundVariables, TypeBinding type, 
			int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.quantifier = quantifier;
		this.range = range;
		this.body = body;
		this.boundVariables = boundVariables;
		Utils.assertTrue(this.range != this.body, "range == body"); //$NON-NLS-1$
	}

	public VC accept(WlpVisitor visitor) {
		return visitor.visit(this);
	}

	public CfgExpression accept(CfgExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "(" + this.quantifier +  //$NON-NLS-1$
		Arrays.asList(this.boundVariables) + " ; " + //$NON-NLS-1$
		this.range + " ; " + this.body + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public static CfgExpression asBlock(CfgExpression body, CfgVarDecl[] boundVarDecls) {
		CfgExpression result = new CfgQuantifiedExpression(CfgQuantifier.FORALL, CfgBooleanConstant.TRUE, body, boundVarDecls, TypeBinding.BOOLEAN, 0, 0);
		return result;
	}

}
