package org.jmlspecs.jml4.esc.gc.lang.simple;

import java.util.Arrays;

import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.CfgStatement;

public class SimpleGoto extends SimpleStatement {

	public final String[] gotos;

	public SimpleGoto(String[] gotos) {
		super(0);
		this.gotos = gotos;
	}

	public CfgStatement accept(PassifyVisitor visitor, IncarnationMap incarnationMap) {
		return visitor.visit(this, incarnationMap);
	}

	public String toString() {
		return "goto: " + Arrays.asList(this.gotos);  //$NON-NLS-1$
	}
}
