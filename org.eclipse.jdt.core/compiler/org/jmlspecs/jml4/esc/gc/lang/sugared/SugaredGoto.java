package org.jmlspecs.jml4.esc.gc.lang.sugared;

import java.util.Arrays;

import org.jmlspecs.jml4.esc.gc.DesugarLoopVisitor;
import org.jmlspecs.jml4.esc.gc.DesugaringVisitor;
import org.jmlspecs.jml4.esc.gc.SimplifyingVisitor;
import org.jmlspecs.jml4.esc.gc.lang.simple.SimpleStatement;

public class SugaredGoto extends SugaredStatement {

	public static final String[] NOWHERE = new String[0];
	public final String[] gotos;

	public SugaredGoto(String[] gotos) {
		super(0);
		this.gotos = gotos;
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
		return "goto: " + Arrays.asList(this.gotos);  //$NON-NLS-1$
	}
}
