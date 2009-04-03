package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class Procedure extends BoogieNode implements Scope {
	private ArrayList/*<VariableDeclaration>*/ locals;
	private ArrayList/*<VariableDeclaration>*/ arguments;
	private ArrayList/*<Statement>*/ statements;
	private ArrayList/*<Expression>*/ requires;
	private ArrayList/*<Expression>*/ ensures;
	private ArrayList/*<MapVariableReference>*/ modifies;
	private String name;
	private TypeReference returnType;
	
	public Procedure(String name, TypeReference returnType, ASTNode javaNode, Program scope) {
		super(javaNode, scope);
		this.returnType = returnType;
		this.name = name;
		this.locals = new ArrayList();
		this.arguments = new ArrayList();
		this.statements = new ArrayList();
		this.ensures = new ArrayList();
		this.requires = new ArrayList();
		this.modifies = new ArrayList();
	}
	
	public TypeReference getReturnType() {
		return returnType;
	}
	
	public ArrayList getLocals() {
		return locals;
	}
	
	public ArrayList getArguments() {
		return arguments;
	}
	
	public ArrayList getStatements() {
		return statements;
	}

	public ArrayList getModifies() {
		return modifies;
	}

	public ArrayList getRequires() {
		return requires;
	}

	public ArrayList getEnsures() {
		return ensures;
	}

	public String getName() {
		return name;
	}
	
	private void printArguments(BoogieSource out) {
		out.append(TOKEN_LPAREN);
		for (int i = 0; i < getArguments().size(); i++) {
			((VariableDeclaration)getArguments().get(i)).toBuffer(out);
			if (i < getArguments().size() - 1) {
				out.append(TOKEN_COMMA + TOKEN_SPACE);
			}
		}
		out.append(TOKEN_RPAREN + TOKEN_SPACE);
	}
	
	private void printReturns(BoogieSource out) {
		if (getReturnType() == null) return;
		out.append("returns" + TOKEN_SPACE + TOKEN_LPAREN); //$NON-NLS-1$
		out.append(TOKEN_RESULT + TOKEN_COLON + TOKEN_SPACE);
		getReturnType().toBuffer(out);
		out.append(TOKEN_RPAREN + TOKEN_SPACE);
	}

	private void printSpec(BoogieSource out, String specName, ArrayList exprs) {
		if (exprs.size() == 0) return;
		for (int i = 0; i < exprs.size(); i++) {
			Expression expr = (Expression)exprs.get(i);
			out.append(specName + TOKEN_SPACE, expr.getJavaNode());
			expr.toBuffer(out);
			out.append(TOKEN_SEMICOLON + TOKEN_SPACE);
		}
	}
	
	private void printModifies(BoogieSource out) {
		if (getModifies().size() == 0) return;
		for (int i = 0; i < getModifies().size(); i++) {
			MapVariableReference ref = (MapVariableReference)getModifies().get(i);
			out.append("modifies" + TOKEN_SPACE, ref.getJavaNode()); //$NON-NLS-1$
			out.append(ref.getName() + TOKEN_SEMICOLON + TOKEN_SPACE);
		}
	}

	public void toBuffer(BoogieSource out) {
		out.append("procedure" + TOKEN_SPACE + getName()); //$NON-NLS-1$

		printArguments(out);
		printReturns(out);
		printModifies(out);
		printSpec(out, "requires", getRequires()); //$NON-NLS-1$
		printSpec(out, "ensures", getEnsures()); //$NON-NLS-1$
		
		// statements
		out.appendLine(TOKEN_LBRACE);
		out.increaseIndent();
		for (int i = 0; i < statements.size(); i++) {
			((Statement)statements.get(i)).toBuffer(out);
		}
		out.decreaseIndent();
		out.appendLine(TOKEN_RBRACE);
	}

	public TypeDeclaration lookupType(String typeName) {
		return getProgramScope().lookupType(typeName);
	}

	public VariableDeclaration lookupVariable(String variableName) {
		for (int i = 0; i < getLocals().size(); i++) {
			VariableDeclaration var = (VariableDeclaration)getLocals().get(i);
			if (var.getName().getName().equals(variableName)) {
				return var; 
			}
		}
		
		return getProgramScope().lookupVariable(variableName);
	}
	
	public Procedure lookupProcedure(String procName) {
		return getProgramScope().lookupProcedure(procName);
	}

	public void addType(TypeDeclaration type) {
		getScope().addType(type);
	}

	public void addVariable(VariableDeclaration decl) {
		getLocals().add(decl);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			for (int i = 0; i < getArguments().size(); i++) {
				((BoogieNode)getArguments().get(i)).traverse(visitor);
			}
			if (getReturnType() != null) {
				getReturnType().traverse(visitor);
			}
			for (int i = 0; i < getModifies().size(); i++) {
				((BoogieNode)getModifies().get(i)).traverse(visitor);
			}
			for (int i = 0; i < getRequires().size(); i++) {
				((BoogieNode)getRequires().get(i)).traverse(visitor);
			}
			for (int i = 0; i < getEnsures().size(); i++) {
				((BoogieNode)getEnsures().get(i)).traverse(visitor);
			}
			for (int i = 0; i < getLocals().size(); i++) {
				((BoogieNode)getLocals().get(i)).traverse(visitor);
			}
			for (int i = 0; i < getStatements().size(); i++) {
				((BoogieNode)getStatements().get(i)).traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}

	public Procedure getProcedureScope() {
		return this;
	}

	public Program getProgramScope() {
		return (Program)getScope();
	}
}
