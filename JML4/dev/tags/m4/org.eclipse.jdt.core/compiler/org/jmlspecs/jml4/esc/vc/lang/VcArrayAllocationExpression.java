package org.jmlspecs.jml4.esc.vc.lang;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcArrayAllocationExpression extends VC {

	public final int[] ids; 
	public final VC[] dims;
	
	public VcArrayAllocationExpression(int[] ids, VC[] dims, TypeBinding type, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(type, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.ids = ids;
		this.dims = dims;
	}
	public VcArrayAllocationExpression(int[] ids, VC[] dims, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.ids = ids;
		this.dims = dims;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public int hashCode() {
		if (true) throw new RuntimeException("why is this here?"); //$NON-NLS-1$
		return 0;
	}

	/*package*/ VC inline(Map map) {
		int length = this.dims.length;
		VC[] inlinedDims = new VC[length];
		for (int i = 0; i < inlinedDims.length; i++) {
			inlinedDims[i] = this.dims[i].inlineAndAddDecls(map);
		}
		return new VcArrayAllocationExpression(this.ids, inlinedDims, this.type, this.kindOfAssertion(), this.kindOfLabel, this.sourceStart, this.sourceEnd, this.labelStart());
	}

	public String toString() {
		String sType = this.type.debugName();
		String sDims = getDimsAsString();
		return "new "+sType+sDims; //$NON-NLS-1$
	}

	private String getDimsAsString() {
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < this.dims.length; i++) {
			result.append("["+this.dims[i]+"]");  //$NON-NLS-1$//$NON-NLS-2$
		}
		return result.toString();
	}

}
