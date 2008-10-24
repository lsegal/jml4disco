package org.jmlspecs.jml4.esc.gc.lang.sugared;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;
import org.jmlspecs.jml4.esc.gc.lang.sugared.expr.SugaredExpression;

public class SugaredWhileStatement extends SugaredStatement {

	public final String label;
	public final SugaredExpression condition;
	public final SugaredLoopAnnotations annotations;
	public final SugaredStatement action;
	
	public SugaredWhileStatement(String label, SugaredExpression condition, SugaredLoopAnnotations annotations, SugaredStatement action, int sourceStart) {
		super(sourceStart);
		this.condition = condition;
		this.annotations = annotations;
		this.action = action;
		this.label = label;
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
		return "[SugaredWhileStatement: ("+this.condition+")\n" + //$NON-NLS-1$ //$NON-NLS-2$
               "\t"+this.annotations+"\n"+  //$NON-NLS-1$//$NON-NLS-2$
	           "\t"+this.action+"\n"+ //$NON-NLS-1$ //$NON-NLS-2$
	           "]"; //$NON-NLS-1$
	}
}
