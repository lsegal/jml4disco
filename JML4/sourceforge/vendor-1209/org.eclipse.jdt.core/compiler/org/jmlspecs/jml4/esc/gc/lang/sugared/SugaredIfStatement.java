package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;

public class SugaredIfStatement extends SugaredStatement {

	public final SugaredExpression condition;
	public final SugaredStatement  thenStatement;
	public final SugaredStatement  elseStatement;
	
	public SugaredIfStatement(SugaredExpression condition, SugaredStatement thenStatement, SugaredStatement elseStatement, int sourceStart) {
		super(sourceStart);
		this.condition = condition;
		this.thenStatement = thenStatement;
		this.elseStatement = elseStatement;
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
		return "[SugaredIfStatement: ("+this.condition+")\n" + //$NON-NLS-1$ //$NON-NLS-2$
 	           "\tthen: "+this.thenStatement+"\n"+  //$NON-NLS-1$//$NON-NLS-2$
		       "\telse: "+this.elseStatement+"\n"+ //$NON-NLS-1$ //$NON-NLS-2$
		       "]"; //$NON-NLS-1$
	}
}
