package org.jmlspecs.jml4.esc.gc.lang;

import java.util.Arrays;

import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgGoto extends CfgStatement {

	public final String[] gotos;
	public CfgGoto(String[] gotos) {
		super(0);
		this.gotos = gotos;
	}

	public VC accept(WlpVisitor visitor, VC N) {
		return visitor.visit(this, N);
	}

	public String toString() {
		return "goto: " + Arrays.asList(this.gotos);  //$NON-NLS-1$
	}

}
