package org.jmlspecs.jml4.boogie.ast;

import java.util.ArrayList;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.jmlspecs.jml4.boogie.BoogieSource;

public class CallStatement extends Statement {
	private String procName;
	private VariableReference outVar;
	private ArrayList/*<Expression>*/ arguments;

	public CallStatement(String procName, Expression[] args, VariableReference outVar, ASTNode javaNode, Scope scope) {
		super(javaNode, scope);
		this.procName = procName;
		this.arguments = new ArrayList();
		this.outVar = outVar;
		if (args != null) {
			for (int i = 0; i < args.length; i++) {
				this.arguments.add(args[i]);
			}
		}
	}
	
	public String getProcedureName() {
		return procName;
	}
	
	public ArrayList getArguments() {
		return arguments;
	}
	
	public VariableReference getOutVar() {
		return outVar;
	}
	
	public void setOutVar(VariableReference outVar) {
		this.outVar = outVar;
	}

	public void toBuffer(BoogieSource out) {
		out.append("call" + TOKEN_SPACE, getJavaNode()); //$NON-NLS-1$
		if (getOutVar() != null) {
			getOutVar().toBuffer(out);
			out.append(TOKEN_SPACE + TOKEN_COLON + TOKEN_EQUALS + TOKEN_SPACE);
		}
		out.append(getProcedureName());
		out.append(TOKEN_LPAREN);
		for (int i = 0; i < getArguments().size(); i++) {
			((Expression)getArguments().get(i)).toBuffer(out);
			if (i < getArguments().size() - 1) {
				out.append(TOKEN_COMMA + TOKEN_SPACE);
			}
		}
		out.appendLine(TOKEN_RPAREN + TOKEN_SEMICOLON);
	}

	public void traverse(Visitor visitor) {
		if (visitor.visit(this)) {
			for (int i = 0; i < getArguments().size(); i++) {
				((BoogieNode)getArguments().get(i)).traverse(visitor);
			}
		}
		visitor.endVisit(this);
	}
}
