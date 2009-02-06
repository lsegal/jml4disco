package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;
import org.jmlspecs.jml4.esc.util.Utils;

public class SugaredReturnStatement extends SugaredStatement {

	public static final String RETURN_BLOCK = "return"; //$NON-NLS-1$
	public final /*@nullable*/ SugaredExpression expr;
	public final /*@nullable*/ TypeBinding type;
	
	public SugaredReturnStatement(/*@nullable*/ SugaredExpression expr, /*@nullable*/ TypeBinding type, int sourceStart) {
		super(sourceStart);
		Utils.assertTrue((expr == null) == (type == TypeBinding.VOID), "expr("+expr+") is of type '"+type+"'");   //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
		this.expr = expr;
		this.type = type;
	}

	public SimpleStatement accept(DesugaringVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredStatement accept(SimplifyingVisitor visitor) {
		return visitor.visit(this);
	}

	public SugaredStatement accept(DesugarLoopVisitor visitor, SugaredStatement rest) {
		return visitor.visit(this, rest);
	}

	public String toString() {
		String sExpr = (expr==null 
				     ?  ""  //$NON-NLS-1$
				     : (expr.toString() + ":" + type.toString())); //$NON-NLS-1$
		return "[return: "+sExpr+"]";  //$NON-NLS-1$//$NON-NLS-2$
	}

}
