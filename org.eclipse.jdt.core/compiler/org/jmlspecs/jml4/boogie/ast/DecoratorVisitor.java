package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.jmlspecs.jml4.boogie.ast.Assignment;
import org.jmlspecs.jml4.boogie.ast.BoogieNode;
import org.jmlspecs.jml4.boogie.ast.CallStatement;
import org.jmlspecs.jml4.boogie.ast.Procedure;
import org.jmlspecs.jml4.boogie.ast.VariableDeclaration;
import org.jmlspecs.jml4.boogie.ast.VariableReference;
import org.jmlspecs.jml4.boogie.ast.VariableStatement;
import org.jmlspecs.jml4.boogie.ast.Visitor;

public class DecoratorVisitor extends Visitor {
	public boolean visit(Procedure term) {
		resolveProcedureLocals(term.getLocals());
		
		// arguments must be added after locals traversal
		for (int i = 0; i < term.getArguments().size(); i++) {
			VariableDeclaration var = (VariableDeclaration)term.getArguments().get(i);
			resolveProcedureArguments(var);
		}
		
		// traverse statements
		for (int i = 0; i < term.getStatements().size(); i++) {
			((BoogieNode)term.getStatements().get(i)).traverse(this);
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
					proc.getStatements().add(0, new VariableStatement(decl, null, proc));
					term.setOutVar(decl.getName());
				}
			}
		}
		return false;
	}
	
	private void resolveProcedureArguments(VariableDeclaration var) {
		var.getScope().addVariable(var);
	}

	private void resolveProcedureLocals(ArrayList vars) {
		for (int i = 0; i < vars.size(); i++) {
			VariableDeclaration var = (VariableDeclaration)vars.get(i);
			Procedure proc = var.getScope().getProcedureScope();
			proc.getStatements().add(0, new VariableStatement(var, var.getJavaNode(), proc));
		}
	}
}
