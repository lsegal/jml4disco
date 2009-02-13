package org.jmlspecs.jml4.esc.vc.lang;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcAndNary extends VC {

	public final VC[] conjuncts;

	public VcAndNary(VC[] conjuncts, int sourceStart, int sourceEnd) {
		super(TypeBinding.BOOLEAN, sourceStart, sourceEnd);
		this.conjuncts = conjuncts;
		for (int i = 0; i < conjuncts.length; i++) {
			List decls = this.conjuncts[i].decls();
			this.addDecls(decls);
			decls.clear();
		}
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
			if (inlined[i] != this.conjuncts[i])
				changed = true;
		}
		if (! changed)
			return this;
		return new VcAndNary(inlined, this.sourceStart, this.sourceEnd);
	}

	public String toString() {
		return declString() + "[/\\" + Arrays.asList(this.conjuncts) + "]"; //$NON-NLS-1$ //$NON-NLS-2$
	}

}
