package org.jmlspecs.jml4.ast;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;

public class JmlSpecCaseHeader extends ASTNode {

	public final JmlRequiresClause[] requiresClauses;

	public JmlSpecCaseHeader(JmlRequiresClause[] requires) {
		this.requiresClauses = requires;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		for (int i = 0; i < requiresClauses.length; i++) {
			output.append(this.requiresClauses[i]);
		}
		return output;
	}

	public void analysePrecondition(MethodScope scope, FlowContext methodContext, FlowInfo flowInfo) {
		for (int i = 0; i < requiresClauses.length; i++) {
			this.requiresClauses[i].analyseCode(scope, methodContext, flowInfo);
		}
	}

	public void generateCheckOfPrecondition(MethodScope methodScope, AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		for (int i = 0; i < requiresClauses.length; i++) {
			this.requiresClauses[i].generateCheck(methodScope, methodDeclaration, codeStream);
		}
	}

	public void resolve(MethodScope scope) {
		for (int i = 0; i < requiresClauses.length; i++) {
			this.requiresClauses[i].resolve(scope);
		}
	}

	public List/*<Expression>*/ getRequiresExpressions() {
		List/*<Expression>*/ result = new ArrayList/*<Expression>*/();
		for (int i = 0; i < requiresClauses.length; i++) {
			result.add(this.requiresClauses[i].expr);
		}
		return result;
	}
}
