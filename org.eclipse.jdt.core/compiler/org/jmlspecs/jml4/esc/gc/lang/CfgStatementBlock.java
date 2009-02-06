package org.jmlspecs.jml4.esc.gc.lang;

import java.util.Arrays;

import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgStatementBlock extends CfgStatement {

	public final CfgStatement stmt;
	public final CfgVarDecl[] boundVarDecls;
	public CfgStatementBlock(CfgStatement stmt, CfgVarDecl[] boundVarDecls) {
		super(stmt.sourceStart);
		this.stmt = stmt;
		this.boundVarDecls = boundVarDecls;
	}

	public VC accept(WlpVisitor visitor, VC N) {
		return visitor.visit(this, N);
	}

	public String toString() {
		return "[CfgStatementBlock: ["+Arrays.asList(this.boundVarDecls)+"]'"+this.stmt.toString()+"']"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
