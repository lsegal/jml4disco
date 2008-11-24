package org.jmlspecs.jml4.esc.vc.lang;

import java.io.Serializable;

import org.jmlspecs.jml4.esc.util.Utils;




//DISCO Serializable
public class VcOperator implements Serializable{
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

	public final String  name;
	public final boolean isEqualityOp;
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
	// DISCO Custom Serialization 
	public static VcOperator getCanonical(VcOperator operator) {
	
		if (operator.name.equals(VcOperator.DIVIDE.name)) 
			return VcOperator.DIVIDE;
		else if(operator.name.equals(VcOperator.EQUALS.name))
			return VcOperator.EQUALS;
		else if (operator.name.equals(VcOperator.EQUIV.name))
			return VcOperator.EQUIV;
		else if (operator.name.equals(VcOperator.GREATER.name))
			return VcOperator.GREATER;
		else if (operator.name.equals(VcOperator.GREATER_EQUALS.name))
			return VcOperator.GREATER_EQUALS;
		else if (operator.name.equals(VcOperator.IMPLIES.name))
			return VcOperator.IMPLIES;
		else if (operator.name.equals(VcOperator.LESS.name))
			return VcOperator.LESS;
		else if (operator.name.equals(VcOperator.LESS_EQUALS.name))
			return VcOperator.LESS_EQUALS;
		else if (operator.name.equals(VcOperator.MINUS.name))
			return VcOperator.MINUS;
		else if (operator.name.equals (VcOperator.NOT_EQUALS.name))
			return VcOperator.NOT_EQUALS;
		else if (operator.name.equals (VcOperator.NOT_EQUIV.name))
			return VcOperator.NOT_EQUIV;
		else if (operator.name.equals (VcOperator.PLUS.name))
			return VcOperator.PLUS;
		else if (operator.name.equals (VcOperator.REMAINDER.name))
			return VcOperator.REMAINDER;
		else if (operator.name.equals (VcOperator.TIMES.name))
			return VcOperator.TIMES;
		else
			Utils.assertTrue(false, "No match for operator name: '" + operator.name + "'"); //$NON-NLS-1$ //$NON-NLS-2$
			return null;
	
	}
}

