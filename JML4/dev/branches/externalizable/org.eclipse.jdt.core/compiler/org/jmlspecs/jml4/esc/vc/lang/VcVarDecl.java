package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;
import org.jmlspecs.jml4.esc.util.Utils;

public class VcVarDecl extends VC {
	public static final VcVarDecl[] EMPTY = new VcVarDecl[0];
	public String name;
	public int    pos;

	public VcVarDecl() {}
	
	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		super.readExternal(in);
		this.name = (String) in.readObject();
		this.pos = in.readInt();
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		super.writeExternal(out);
		out.writeObject(this.name);
		out.writeInt(this.pos);
	}
	
	public VcVarDecl(String name, int pos, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.name = name;
		this.pos  = pos;
	}

	public String toString() {
		return "[VCVarDecl: "+this.name+" :: "+this.type.debugName()+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}
	public String accept(ProverVisitor visitor, int max) {
		return visitor.visit(this, max);
	}
	public String accept(ProverVisitor visitor) {
		Utils.assertTrue(false, "shouldn't be called"); //$NON-NLS-1$
		return ""; //$NON-NLS-1$
	}
	/*package*/ VC inline(Map map) {
		return this;
	}
	public int hashCode() {
		final int prime = 31;
		int result;
		result = prime * type.toString().hashCode() + name.hashCode();
		return result;
	}

	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!(obj instanceof VcVarDecl))
			return false;
		return this.name.equals(((VcVarDecl)obj).name);
	}
}
