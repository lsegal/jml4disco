package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcArrayReference extends VC {

	public VC receiver;
	public VC position;
	public int incarnation;
	
	public VcArrayReference () {}

	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		super.readExternal(in);
		this.receiver = readVc(in);
		this.position = readVc(in);
		this.incarnation = in.readInt();
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		super.writeExternal(out);
		this.receiver.writeVc(out);
		this.position.writeVc(out);
		out.writeInt(this.incarnation);
	}
	
	public VcArrayReference(VC receiver, VC position, int incarnation, TypeBinding type, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(type, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.receiver = receiver;
		this.position = position;
		this.incarnation = incarnation;
	}

	public VcArrayReference(VC receiver, VC position, int incarnation, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.receiver = receiver;
		this.position = position;
		this.incarnation = incarnation;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	//* all array references are equal (for now), but why is this needed ??
	public int hashCode() {
		int aNotTooBigPrime = 100000019;
		return aNotTooBigPrime;
	}

	VC inline(Map map) {
		VC inlinedReceiver = this.receiver.inlineAndAddDecls(map);
		VC inlinedPosition = this.position.inlineAndAddDecls(map);
		return inlinedReceiver.equals(this.receiver) && inlinedPosition.equals(this.position)
		     ? this
		     : new VcArrayReference(inlinedReceiver, inlinedPosition, this.incarnation, this.type, this.sourceStart, this.sourceEnd);
	}

	public String toString() {
		return "{"+this.receiver+"[|"+this.position+"|]}";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
	}

}
