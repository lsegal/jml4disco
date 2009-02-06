package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcNot extends VC {

	public VC vc;

	public VcNot () {}

	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		super.readExternal(in);
		this.vc = readVc(in);
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		super.writeExternal(out);
		this.vc.writeVc(out);
	}
	
	public VcNot(VC vc, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(vc.type, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.vc = vc;
	}

	public VcNot(VC vc, int sourceStart, int sourceEnd) {
		super(vc.type, sourceStart, sourceEnd);
		this.vc = vc;
	}

	public String toString() {
		return declString() + "(! " + this.vc + ")"; //$NON-NLS-1$ //$NON-NLS-2$
	}
	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}
	public String acceptAsTerm(ProverVisitor visitor) {
		return visitor.visitAsTerm(this);
	}
	public List/*<VcVarDecl>*/ getVarDecls() {
		List/*<VcVarDecl>*/ result= new ArrayList/*<VcVarDecl>*/();
		result.addAll(this.decls());
		result.addAll(this.vc.decls());
		return result;
	}
	/*package*/ VC inline(Map map) {
		// remove double negative
// need to copy over some things, like kind of error etc.
//		if (this.vc instanceof VcNot)
//			return ((VcNot) this.vc).vc.inline(map);
		VC vcs = this.vc.inlineAndAddDecls(map);
		if (this.vc.equals(vcs))
			return this;
		return new VcNot(vcs, this.sourceStart, this.sourceEnd);
	}
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * prime * result + ((vc == null) ? 0 : vc.hashCode());
		return result;
	}
}
