package org.jmlspecs.jml4.fspv.theory;

public class TheoryType {

	private static final String	INT	= "int"; //$NON-NLS-1$
	private static final String	NAT	= "nat"; //$NON-NLS-1$
	private static final String	BOOL	= "bool"; //$NON-NLS-1$
	public static final String	TYPE_SEPARATOR	= " :: "; //$NON-NLS-1$
	private String	type;
	
	private TheoryType(String type) {
		this.type = type;
	}

	public boolean isInt() {
		return this.type.equals(INT);
	}

	public boolean isNat() {
		return this.type.equals(NAT);
	}

	public boolean isBool() {
		return this.type.equals(BOOL);
	}

	public String toString() {
		return type;
	}

	public static TheoryType Int() {
		return new TheoryType(INT);
	}

	public static TheoryType Nat() {
		return new TheoryType(NAT);
	}

	public static TheoryType Bool() {
		// TODO Auto-generated method stub
		return new TheoryType(BOOL);
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
