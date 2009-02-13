package org.jmlspecs.jml4.fspv.simpl.ast;

public class SimplHoareState extends SimplState {

	public static final SimplHoareState MEMORY = new SimplHoareState("memory",  //$NON-NLS-1$
			new SimplGlobalVariable[]{SimplGlobalVariable.ALLOC, SimplGlobalVariable.FREE});

	public final String name;
	public final SimplGlobalVariable[] fields;
	public final SimplHoareState in;

	public SimplHoareState(String name, SimplGlobalVariable[] fields) {
		this(name, fields, null);
	}

	public SimplHoareState(String name, SimplGlobalVariable[] fields, SimplHoareState in) {
		this.name = name;
		this.fields = fields;
		this.in = in;
	}

}
