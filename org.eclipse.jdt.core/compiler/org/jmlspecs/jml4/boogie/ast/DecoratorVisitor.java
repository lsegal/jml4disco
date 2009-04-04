package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

public class DecoratorVisitor extends Visitor {
	public boolean visit(Program term) {
		for (int i = 0; i < term.getTypes().size(); i++) {
			resolveTypes((TypeDeclaration)term.getTypes().get(i));
		}

		for (int i = 0; i < term.getProcedures().size(); i++) {
			((BoogieNode)term.getProcedures().get(i)).traverse(this);
		}
		return false;
	}
	
	public boolean visit(Procedure term) {
		// traverse statements first (might generate new locals here)
		for (int i = 0; i < term.getStatements().size(); i++) {
			((BoogieNode)term.getStatements().get(i)).traverse(this);
		}

		resolveProcedureLocals(term.getLocals());
		
		// arguments must be added after locals traversal
		for (int i = 0; i < term.getArguments().size(); i++) {
			VariableDeclaration var = (VariableDeclaration)term.getArguments().get(i);
			resolveProcedureArguments(var);
		}
		
		return false;
	}
	
	public boolean visit(Assignment term) {
		VariableDeclaration decl = term.getScope().lookupVariable(term.getVariable().getName());
		if (decl != null && !decl.isLocal()) {
			Procedure proc = term.getScope().getProcedureScope();
			proc.getModifies().add(decl.getName());
		}
		return false;
	}
	
	public boolean visit(CallStatement term) {
		if (term.getOutVar() == null) {
			Procedure calledProcedure = term.getScope().lookupProcedure(term.getProcedureName());
			if (calledProcedure != null) { // calledProcedure should not be null
				if (calledProcedure.getReturnType() != null) {
					// need to declare a variable
					Procedure proc = term.getScope().getProcedureScope();
					String varName = "$unused_" + proc.getLocals().size(); //$NON-NLS-1$
					VariableDeclaration decl = new VariableDeclaration(
							new VariableReference(varName, null, proc),  
							calledProcedure.getReturnType(), proc);
					proc.addVariable(decl);
					term.setOutVar(decl.getName());
				}
			}
		}
		return false;
	}
	
	private void resolveTypes(TypeDeclaration term) {
		ArrayList stmts = term.getScope().getProgramScope().getStatements();
		stmts.add(new ConstStatement(term, null, term.getScope()));
		stmts.add(new Axiom(new BinaryExpression(new TokenLiteral(
				term.getType().getTypeName()), "<:", //$NON-NLS-1$
				new TokenLiteral(term.getSuperType().getTypeName()), 
				false, null, term.getScope()), null, term.getScope()));
	}
	
	private void resolveProcedureArguments(VariableDeclaration var) {
		var.getScope().addVariable(var);
		
		// type requirements
		// TODO add support for array types
		if (!(var.getType() instanceof MapTypeReference) && !var.getType().isNative()) {
			Procedure proc = var.getScope().getProcedureScope();
			BinaryExpression expr = new BinaryExpression(
					new FunctionCall("$dtype", new Expression[] { var.getName() }, var.getJavaNode(), proc),  //$NON-NLS-1$
					"==", new TokenLiteral(var.getType().getTypeName()), false, null, proc); //$NON-NLS-1$
			proc.getRequires().add(expr);
		}
	}

	private void resolveProcedureLocals(ArrayList vars) {
		for (int i = 0; i < vars.size(); i++) {
			VariableDeclaration var = (VariableDeclaration)vars.get(i);
			Procedure proc = var.getScope().getProcedureScope();
			proc.getStatements().add(0, new VariableStatement(var, var.getJavaNode(), proc));
		}
	}
}
