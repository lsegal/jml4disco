package org.jmlspecs.jml4.esc.gc.lang.simple.expr;

import java.util.Arrays;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.SimpleExprVisitor;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleVarDecl;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleQuantifiedExpression extends SimpleExpression {

	public final SimpleQuantifier quantifier;
	public final SimpleExpression range;
	public final SimpleExpression body;
	public final SimpleVarDecl[] boundVariables;

	public SimpleQuantifiedExpression(SimpleQuantifier quantifier, SimpleExpression range, 
			SimpleExpression body, SimpleVarDecl[] boundVariables, TypeBinding type, 
			int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.quantifier = quantifier;
		this.range = range;
		this.body = body;
		this.boundVariables = boundVariables;
		Utils.assertTrue(this.range != this.body, "range == body"); //$NON-NLS-1$
	}

	public CfgExpression accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public SimpleExpression accept(SimpleExprVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "(" + this.quantifier +  //$NON-NLS-1$
			Arrays.asList(this.boundVariables) + " ; " + //$NON-NLS-1$
			this.range + " ; " + this.body + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
