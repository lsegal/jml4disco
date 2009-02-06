package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import java.util.Arrays;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.gc.lang.sugared.SugaredVarDecl;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredQuantifiedExpression extends SugaredExpression {

	public final SugaredQuantifier quantifier;
	public final SugaredExpression range;
	public final SugaredExpression body;
	public final SugaredVarDecl[] boundVariables;

	public SugaredQuantifiedExpression(SugaredQuantifier quantifier,
			SugaredExpression range, SugaredExpression body,
			SugaredVarDecl[] boundVariables, TypeBinding type, 
			int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.quantifier = quantifier;
		this.range = range;
		this.body = body;
		this.boundVariables = boundVariables;
		Utils.assertTrue(this.range != this.body, "range == body"); //$NON-NLS-1$
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "(" + this.quantifier +  //$NON-NLS-1$
			Arrays.asList(this.boundVariables) + " ; " + //$NON-NLS-1$
			this.range + " ; " + this.body + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}
}
