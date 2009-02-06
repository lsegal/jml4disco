package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcFieldReference extends VC {

	public  VC receiver;
	public  String field;
	public  int incarnation;

	public VcFieldReference () {}

	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		super.readExternal(in);
		this.receiver = readVc(in);
		this.field =  (String) in.readObject();
		this.incarnation = in.readInt();
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		super.writeExternal(out);
		this.receiver.writeVc(out);
		out.writeObject(this.field);
		out.writeInt(this.incarnation);
	}
	
	public VcFieldReference(VC receiver, String field, int incarnation, TypeBinding type, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(type, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.receiver = receiver;
		this.field = field;
		this.incarnation = incarnation;
	}

	public VcFieldReference(VC receiver, String field, int incarnation, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.receiver = receiver;
		this.field = field;
		this.incarnation = incarnation;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public int hashCode() {
		int prime = 31;
		int result = 1;
		result = result * prime + receiver.hashCode();
		result = result * prime + field.hashCode();
		result = result * prime + this.sourceStart;
		return result;
	}

	VC inline(Map map) {
		VC inlinedReceiver = this.receiver.inlineAndAddDecls(map);
		return inlinedReceiver.equals(this.receiver)
		     ? this
		     : new VcFieldReference(inlinedReceiver, this.field, this.incarnation, this.type, this.sourceStart, this.sourceEnd);
	}

	public String toString() {
		return "["+this.receiver+"."+this.field+"("+this.incarnation+")]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

}
