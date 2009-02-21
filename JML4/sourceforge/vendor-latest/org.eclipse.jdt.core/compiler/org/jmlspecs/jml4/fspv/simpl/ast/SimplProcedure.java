package org.jmlspecs.jml4.fspv.simpl.ast;

public class SimplProcedure extends SimplTheoryNode {

	public final String name;
	public final SimplState state;
	public final SimplArgument[] arguments;
	public final SimplLocalVariables[] locals;
	public final SimplStatement[] statements;

	public SimplProcedure(String name, SimplState state, SimplArgument[] args,
			SimplLocalVariables[] locals, SimplStatement[] ss) {
		this.name = name;
		this.state = state;
		this.arguments = args;
		this.locals = locals;
		this.statements = ss;
	}

}
