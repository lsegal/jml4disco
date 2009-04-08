package org.jmlspecs.jml4.esc.vc.lang;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcArrayReference extends VC {

	public final VC receiver;
	public final VC position;
	public final int incarnation;

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
		return inlinedReceiver == this.receiver && inlinedPosition == this.position
		     ? this
		     : new VcArrayReference(inlinedReceiver, inlinedPosition, this.incarnation, this.type, this.sourceStart, this.sourceEnd);
	}

	public String toString() {
		return "{"+this.receiver+"[|"+this.position+"|]$"+this.incarnation+"}";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

}
