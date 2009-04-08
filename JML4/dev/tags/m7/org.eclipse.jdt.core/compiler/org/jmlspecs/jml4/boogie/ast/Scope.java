package org.jmlspecs.jml4.boogie.ast;

public interface Scope {
	public Program getProgramScope();
	public Procedure getProcedureScope();
	
	public VariableDeclaration lookupVariable(String name);
	public TypeDeclaration lookupType(String name);
	public Procedure lookupProcedure(String name);
	public FunctionDeclaration lookupFunction(String name);
	
	public void addVariable(VariableDeclaration decl);
	public void addType(TypeDeclaration type);
	public void addFunction(FunctionDeclaration function);
}
