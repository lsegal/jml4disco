package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcFieldStore extends VC {

	public VcFieldReference field;
	public int oldIncarnation;
	public int newIncarnation;
	public VC value;

	public VcFieldStore () {}

	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		super.readExternal(in);
		this.field = new VcFieldReference();
		this.field.readExternal(in);
		this.oldIncarnation = in.readInt();
		this.newIncarnation = in.readInt();
		this.value = readVc(in);
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		super.writeExternal(out);
		this.field.writeExternal(out);
		out.writeInt(this.oldIncarnation);
		out.writeInt(this.newIncarnation);
		this.value.writeVc(out);
	}
	
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
