package org.jmlspecs.jml4.esc.gc.lang.simple;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;
import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleVariable;

public class SimpleHavoc extends SimpleStatement {
	public final SimpleVariable var;

	public SimpleHavoc(SimpleVariable var, int sourceStart) {
		super(sourceStart);
		this.var = var;
	}

	public CfgStatement accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public String toString() {
		return "[SimpleHavoc: " + this.var + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
