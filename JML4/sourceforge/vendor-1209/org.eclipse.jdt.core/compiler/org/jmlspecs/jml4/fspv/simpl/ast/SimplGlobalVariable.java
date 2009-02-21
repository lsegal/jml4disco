package org.jmlspecs.jml4.fspv.simpl.ast;

public class SimplGlobalVariable extends SimplVariable {

	public SimplGlobalVariable(String name, SimplType type) {
		super(name, type);
		// TODO Auto-generated constructor stub
	}
	
	public static final SimplGlobalVariable FREE = new SimplGlobalVariable("free", new SimplNatType()); //$NON-NLS-1$
	public static final SimplGlobalVariable ALLOC = new SimplGlobalVariable("alloc",  //$NON-NLS-1$
			new SimplTypes(new SimplType[]{new SimplRefType(),new SimplListType()}));


}
