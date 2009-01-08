package org.jmlspecs.jml4.esc.gc.lang.simple;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;

public abstract class SimpleStatement {

	public final int sourceStart;
	public SimpleStatement(int sourceStart) {
		this.sourceStart = sourceStart;
	}
	public abstract CfgStatement accept(PassifyVisitor visitor, IncarnationMap incarnationMap);
	public abstract String toString();
}
