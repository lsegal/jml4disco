package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;
import java.util.Hashtable;

import org.jmlspecs.jml4.boogie.BoogieSource;

public class Program extends BoogieNode implements Scope {
	private boolean expanded;
	private ArrayList/*<TypeDeclaration>*/ types;
	private ArrayList/*<VariableDeclaration>*/ globals;
	private ArrayList/*<Statement>*/ statements;
	private ArrayList/*<Procedure>*/ procedures;
	private ArrayList/*<FunctionDeclaration>*/ functions;
	
	private Hashtable/*<String,TypeDeclaration>*/ typesMap;
	private Hashtable/*<String,VariableDeclaration>*/ globalsMap;
	private Hashtable/*<String,FunctionDeclaration>*/ functionsMap;
	
	public Program() {
		super(null, null);
		this.expanded = false;
		this.types = new ArrayList();
		this.statements = new ArrayList();
		this.procedures = new ArrayList();
		this.globals = new ArrayList();
		this.functions = new ArrayList();
		this.typesMap = new Hashtable();
		this.globalsMap = new Hashtable();
		this.functionsMap = new Hashtable();
	}
	
	public boolean isExpanded() {
		return expanded;
	}
	
	public ArrayList getTypes() {
		return types;
	}

	public ArrayList getStatements() {
		return statements;
	}
	
	public ArrayList getProcedures() {
		return procedures;
	}
	
	public ArrayList getFunctions() {
		return functions;
	}

	public ArrayList getGlobals() {
		return globals;
	}

	public TypeDeclaration lookupType(String name) {
		return (TypeDeclaration)typesMap.get(name);
	}

	public VariableDeclaration lookupVariable(String name) {
		return (VariableDeclaration)globalsMap.get(name);
	}
	
	public FunctionDeclaration lookupFunction(String name) {
		return (FunctionDeclaration)functionsMap.get(name);
	}

	public Procedure lookupProcedure(String name) {
		for (int i = 0; i < getProcedures().size(); i++) {
			Procedure proc = (Procedure)getProcedures().get(i);
			if (proc.getName().equals(name)) {
				return proc;
			}
		}
		return null;
	}

	public void toBuffer(BoogieSource out) {
		resolve(); // resolve before printing buffer out
		for (int i = 0; i < getStatements().size(); i++) {
			((Statement)getStatements().get(i)).toBuffer(out);
		}
		for (int i = 0; i < getFunctions().size(); i++) {
			((FunctionDeclaration)getFunctions().get(i)).toBuffer(out);
		}
		for (int i = 0; i < getProcedures().size(); i++) {
			((Procedure)getProcedures().get(i)).toBuffer(out);
		}
	}
	
	public Program resolve() {
		if (expanded) return this;
		Visitor[] visitors = { new TypeDeclaratorVisitor(), new DecoratorVisitor() };
		for (int i = 0; i < visitors.length; i++) {
			traverse(visitors[i]);
		}
		expanded = true;
		return this;
	}

	public void addType(TypeDeclaration type) {
		if (type.getType().isNative()) return;
		if (type.getType().getTypeName().equals("java.lang.Object")) return; //$NON-NLS-1$
		if (typesMap.get(type.getType().getTypeName()) == null) {
			getTypes().add(type);
			typesMap.put(type.getType().getTypeName(), type);
		}
	}

	public void addVariable(VariableDeclaration decl) {
		if (globalsMap.get(decl.getName().getName()) == null) {
			getGlobals().add(decl);
			globalsMap.put(decl.getName().getName(), decl);
		}
	}
	
	public void addFunction(FunctionDeclaration function) {
		if (functionsMap.get(function.getName()) == null) {
			getFunctions().add(function);
			functionsMap.put(function.getName(), function);
		}
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			for (int i = 0; i < getTypes().size(); i++) {
				((BoogieNode)getTypes().get(i)).traverse(visitor);
			}
			for (int i = 0; i < getGlobals().size(); i++) {
				((BoogieNode)getGlobals().get(i)).traverse(visitor);
			}
			for (int i = 0; i < getFunctions().size(); i++) {
				((BoogieNode)getFunctions().get(i)).traverse(visitor);
			}
			for (int i = 0; i < getStatements().size(); i++) {
				((BoogieNode)getStatements().get(i)).traverse(visitor);
			}
			for (int i = 0; i < getProcedures().size(); i++) {
				((BoogieNode)getProcedures().get(i)).traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

	public Procedure getProcedureScope() {
		return null;
	}

	public Program getProgramScope() {
		return this;
	}
}
