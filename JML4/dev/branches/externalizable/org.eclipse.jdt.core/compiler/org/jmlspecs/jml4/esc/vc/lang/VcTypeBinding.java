package org.jmlspecs.jml4.esc.vc.lang;

import java.io.Externalizable;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;

import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.jmlspecs.jml4.ast.JmlAstUtils;
//DISCO new type to allow serialization
public class VcTypeBinding extends ReferenceBinding implements Externalizable {
	public String strCompounName;
	
	public VcTypeBinding() {}

	public void readExternal(ObjectInput in) throws IOException,
			ClassNotFoundException {
		this.strCompounName = (String) in.readObject();
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		out.writeObject(this.strCompounName);
	}
	
	public VcTypeBinding(char[][] compoundName) {
		this.compoundName = compoundName; 
		strCompounName = JmlAstUtils.concatWith(compoundName, '.');
	}
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result
				+ ((strCompounName == null) ? 0 : strCompounName.hashCode());
		return result;
	}
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!getClass().equals(obj.getClass()))
			return false;
		VcTypeBinding other = (VcTypeBinding) obj;
		if (strCompounName == null) {
			if (other.strCompounName != null)
				return false;
		} else if (!strCompounName.equals(other.strCompounName))
			return false;
		return true;
	}		
}
