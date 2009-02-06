package org.jmlspecs.jml4.ast;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;


public class JmlSpecCaseRestAsClauseSeq extends JmlSpecCaseRest {

	public final JmlClause[] clauses;

	public JmlSpecCaseRestAsClauseSeq(JmlClause[] clauses) {
		this.clauses = clauses;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		for (int i = 0; i < clauses.length; i++) {
			output.append(this.clauses[i]);
		}
		return output;
	}

	public void analysePostcondition(MethodScope scope, FlowContext methodContext, FlowInfo flowInfo) {
		for (int i = 0; i < clauses.length; i++) {
			this.clauses[i].analyseCode(scope, methodContext, flowInfo);
		}
	}

	public void generateCheckOfPostcondition(BlockScope currentScope, AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		for (int i = 0; i < clauses.length; i++) {
			this.clauses[i].generateCheck(currentScope, methodDeclaration, codeStream);
		}
	}

	public void resolve(MethodScope scope) {
		for (int i = 0; i < clauses.length; i++) {
			this.clauses[i].resolve(scope);
		}
	}

	public List/*<Expressioni>*/ getEnsuresExpressions() {
		List/*<Expression>*/ result = new ArrayList/*<Expression>*/();
		for (int i = 0; i < this.clauses.length; i++) {
			JmlClause clause = this.clauses[i];
			if (clause instanceof JmlEnsuresClause) {
				result.add(((JmlEnsuresClause)clause).expr);
			}
		}
		return result;
	}
}
