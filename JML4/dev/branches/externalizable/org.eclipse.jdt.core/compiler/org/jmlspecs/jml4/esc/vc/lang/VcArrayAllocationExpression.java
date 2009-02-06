package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcArrayAllocationExpression extends VC {

	public int[] ids; 
	public VC[] dims;
	
	public VcArrayAllocationExpression() {}
	
	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		super.readExternal(in);
		this.ids = (int[]) in.readObject();
		int numOfDims = in.readInt();
		this.dims = new VC [numOfDims];
		for( int i = 0 ; i < numOfDims ; i++ ) {
			this.dims[i] = readVc(in);
		}
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		super.writeExternal(out);
		out.writeObject(this.ids);
		out.writeInt(this.dims.length);
		for( int i = 0 ; i < this.dims.length ; i++ ) {
			dims[i].writeVc(out);
		}
	}
	
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
