package org.jmlspecs.jml4.esc.gc.lang.sugared.expr;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SugaredExpressionVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredVariable extends SugaredAssignable{

	public final String  name;
	public final int     pos;
	public final boolean isStaticField;

	public SugaredVariable(String name, int pos, TypeBinding type, int sourceStart, int sourceEnd, boolean isStaticField) {
		super(type, sourceStart, sourceEnd);
		this.name = name;
		Utils.assertNotNull(type , "type of "+name+" is null");  //$NON-NLS-1$//$NON-NLS-2$
		Utils.assertTrue(type != TypeBinding.VOID, "type of "+name+" is void"); //$NON-NLS-1$ //$NON-NLS-2$
		this.pos  = pos;
		this.isStaticField = isStaticField;
	}

	public SugaredVariable(String name, int pos, TypeBinding type, int sourceStart, int sourceEnd) {
		this(name, pos, type, sourceStart, sourceEnd, false);
	}

	public SimpleExpression accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredExpression  accept(SugaredExpressionVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return "["+this.name+"]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

	public String getName() {
		return this.name;
	}

	public boolean isVariable() {
		return true;
	}

}
