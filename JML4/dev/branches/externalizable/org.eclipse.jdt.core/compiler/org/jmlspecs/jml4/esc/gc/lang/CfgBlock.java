package org.jmlspecs.jml4.esc.gc.lang;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.IncarnationMap;
import org.jmlspecs.jml4.esc.gc.lang.expr.CfgExpression;
import org.jmlspecs.jml4.esc.util.Utils;
import org.jmlspecs.jml4.esc.vc.WlpVisitor;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class CfgBlock {
	public final String blockId;
	private CfgStatement stmt;
	private final IncarnationMap incarnationMap;

	public CfgBlock(String blockId, CfgStatement stmt, IncarnationMap incarnationMap) {
		super();
		this.blockId = blockId;
		this.stmt = stmt;
		this.incarnationMap = incarnationMap;
	}

	public CfgStatement stmt() {
		return this.stmt;
	}
	public String toString() {
		return "[CfgBlock: " + this.blockId + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
				"\t" + this.stmt + "]"; //$NON-NLS-1$//$NON-NLS-2$
	}

	public VC accept(WlpVisitor visitor, VC N) {
		return visitor.visit(this, N);
	}

	public IncarnationMap getIncarnationMap() {
		return this.incarnationMap;
	}

	public void addAssume(CfgExpression pred) {
		Utils.assertTrue(pred.type == TypeBinding.BOOLEAN, "'"+pred+"' isn't a boolean but a '"+pred.type+"'");  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
		CfgAssume assumption = new CfgAssume(pred, pred.sourceStart);
		this.stmt = new CfgSequence(assumption, this.stmt);
	}
}
