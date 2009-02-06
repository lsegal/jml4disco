package org.jmlspecs.jml4.esc.vc.lang;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcFieldStore extends VC {

	public final VcFieldReference field;
	public final int oldIncarnation;
	public final int newIncarnation;
	public final VC value;

	public VcFieldStore(VcFieldReference field, int oldIncarnation, int newIncarnation, VC value, KindOfAssertion kindOfAssertion, int kindOfLabel, int labelStart) {
		super(TypeBinding.BOOLEAN, kindOfAssertion, kindOfLabel, field.sourceStart, field.sourceEnd, labelStart);
		this.field = field;
		this.oldIncarnation = oldIncarnation;
		this.newIncarnation = newIncarnation;
		this.value = value;
	}

	public VcFieldStore(VcFieldReference field, int oldIncarnation, int newIncarnation, VC value) {
		super(TypeBinding.BOOLEAN, field.sourceStart, field.sourceEnd);
		this.field = field;
		this.oldIncarnation = oldIncarnation;
		this.newIncarnation = newIncarnation;
		this.value = value;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public int hashCode() {
		int prime = 31;
		int result = 1;
		result = result * prime + field.hashCode();
		result = result * prime + oldIncarnation;
		result = result * prime + newIncarnation;
		result = result * prime + value.hashCode();
		result = result * prime + this.sourceStart;
		return result;
	}

	VC inline(Map map) {
		return this;
	}

	public String toString() {
		return "["+this.field.field+"("+newIncarnation+") := " +   //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		"(["+this.field.receiver+"."+this.field.field+"("+oldIncarnation+")] ->"+  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		this.value+")]"; //$NON-NLS-1$
	}

}
