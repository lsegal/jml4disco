package org.jmlspecs.jml4.esc.vc.lang;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcVariable extends VC {

	public final String name;
	public final int pos;
	public final int incarnation;

	public VcVariable(String name, int pos, TypeBinding type, int incarnation, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.name = name;
		this.pos  = pos;
		this.incarnation = incarnation;
	}

	public String toString() {
		return declString() + this.name + "@" + this.pos + "$" + this.incarnation;  //$NON-NLS-1$//$NON-NLS-2$
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}
	public String acceptAsTerm(ProverVisitor visitor) {
		return visitor.visitAsTerm(this);
	}
	/*package*/ VC inline(Map map) {
		VC subst = (VC) map.get(this.name);
		return subst == null
			 ? this
			 : subst.inlineAndAddDecls(map);
	}
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = result * prime + name.hashCode();
		result = result * prime + pos;
		result = result * prime + incarnation;
		return result;
	}
}
