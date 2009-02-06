package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Arrays;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcAndNary extends VC {

	public VC[] conjuncts; 

	public VcAndNary() {}

	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		super.readExternal(in);
		int conjuntsSize = in.readInt();
		conjuncts = new VC [conjuntsSize];
		for(int i = 0 ; i < conjuntsSize ; i++ ) {
			this.conjuncts[i] = readVc(in);
		}
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		super.writeExternal(out);
		out.writeInt(this.conjuncts.length);
		for(int i = 0 ; i < this.conjuncts.length ; i++ ) {
			this.conjuncts[i].writeVc(out);
		}
	}

	public VcAndNary(VC[] conjuncts, int sourceStart, int sourceEnd) {
		super(TypeBinding.BOOLEAN, sourceStart, sourceEnd);
		this.conjuncts = conjuncts;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public int hashCode() {
		final int prime = 17;
		int result = 1;
		for (int i = 0; i < this.conjuncts.length; i++) {
			result = prime * result + this.conjuncts[i].hashCode();
		}
		return result;
	}

	VC inline(Map map) {
		boolean changed = false;
		VC[] inlined = new VC[this.conjuncts.length];
		for (int i = 0; i < this.conjuncts.length; i++) {
			inlined[i] = this.conjuncts[i].inlineAndAddDecls(map);
			if (!inlined[i].equals(this.conjuncts[i]))
				changed = true;
		}
		if (! changed)
			return this;
		return new VcAndNary(inlined, this.sourceStart, this.sourceEnd);
	}

	public String toString() {
		return declString() + "[/\\" + Arrays.asList(this.conjuncts) + "]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
