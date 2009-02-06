package org.jmlspecs.jml4.esc.vc.lang;

import java.io.Externalizable;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;




//DISCO Serializable
public class VcOperator implements Externalizable {
	public static final VcOperator EQUALS         = new VcOperator("==", true); //$NON-NLS-1$
	public static final VcOperator NOT_EQUALS     = new VcOperator("!=", true); //$NON-NLS-1$
	public static final VcOperator GREATER        = new VcOperator(">",  true); //$NON-NLS-1$
	public static final VcOperator GREATER_EQUALS = new VcOperator(">=", true); //$NON-NLS-1$
	public static final VcOperator LESS           = new VcOperator("<",  true); //$NON-NLS-1$
	public static final VcOperator LESS_EQUALS    = new VcOperator("<=", true); //$NON-NLS-1$

	public static final VcOperator PLUS      = new VcOperator("+"); //$NON-NLS-1$
	public static final VcOperator MINUS     = new VcOperator("-"); //$NON-NLS-1$
	public static final VcOperator TIMES     = new VcOperator("*"); //$NON-NLS-1$
	public static final VcOperator DIVIDE    = new VcOperator("/"); //$NON-NLS-1$
	public static final VcOperator REMAINDER = new VcOperator("%"); //$NON-NLS-1$

	public static final VcOperator IMPLIES     = new VcOperator("-->");   //$NON-NLS-1$
	public static final VcOperator EQUIV       = new VcOperator("<-->");  //$NON-NLS-1$
	public static final VcOperator NOT_EQUIV   = new VcOperator("<-!->"); //$NON-NLS-1$

	public String  name;
	public boolean isEqualityOp;

	public VcOperator() {}

	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		this.name = (String) in.readObject();
		this.isEqualityOp = in.readBoolean();
	}
	public void writeExternal(ObjectOutput out) throws IOException {
		out.writeObject(this.name);
		out.writeBoolean(this.isEqualityOp);
	}

	private VcOperator(String name, boolean isEqualityOp) {
		this.name = name;
		this.isEqualityOp = isEqualityOp;
	}
	private VcOperator(String name) {
		this(name, false);
	}
	public String toString() {
		return this.name;
	}
	public int hashCode() {
		return name.hashCode();
	}

	public boolean equals(Object obj) {
		boolean isEquals = false;
		if(obj == null) {
			isEquals = false;
		} else if (! ( obj instanceof VcOperator)) {
			isEquals = false;
		} else {
			VcOperator vcOps = (VcOperator) obj;
			if( vcOps.isEqualityOp == this.isEqualityOp && vcOps.name.equals(this.name)) {
				isEquals = true;
			}
		}
		return isEquals;
	}
}

