package org.jmlspecs.jml4.ast;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;


public class JmlMethodSpecification extends ASTNode {

	public final JmlSpecCase[] specCases;	// main spec cases
	public final JmlSpecCase[] redundantSpecCases;
	public final boolean       isExtending;

	public JmlMethodSpecification(JmlSpecCase[] specCases, JmlSpecCase[] impliedSpecCases, boolean isExtending) {
		this.specCases = specCases;
		this.redundantSpecCases = impliedSpecCases;
		this.isExtending = isExtending;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		for (int i = 0; i < specCases.length; i++) {
			this.specCases[i].print(indent, output);
		}
		printIndent(indent, output).append("implies_that"); //$NON-NLS-1$
		for (int i = 0; i < redundantSpecCases.length; i++) {
			this.redundantSpecCases[i].print(indent+1, output);
		}
		return output;
	}

	public void analysePrecondition(MethodScope scope, FlowContext methodContext, FlowInfo flowInfo) {
		for (int i = 0; i < specCases.length; i++) {
			this.specCases[i].analysePrecondition(scope, methodContext, flowInfo);
		}
		for (int i = 0; i < redundantSpecCases.length; i++) {
			this.redundantSpecCases[i].analysePrecondition(scope, methodContext, flowInfo);
		}
	}
	public void analysePostcondition(MethodScope scope, FlowContext methodContext, FlowInfo flowInfo) {
		for (int i = 0; i < specCases.length; i++) {
			this.specCases[i].analysePostcondition(scope, methodContext, flowInfo);
		}
		for (int i = 0; i < redundantSpecCases.length; i++) {
			this.redundantSpecCases[i].analysePostcondition(scope, methodContext, flowInfo);
		}
	}

	public void resolve(MethodScope scope) {
		for (int i = 0; i < specCases.length; i++) {
			this.specCases[i].resolve(scope);
		}
		for (int i = 0; i < redundantSpecCases.length; i++) {
			this.redundantSpecCases[i].resolve(scope);
		}
	}

	public void generateCheckOfRequires(MethodScope methodScope, AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		if (methodScope.compilerOptions().jmlDbcEnabled && methodScope.compilerOptions().jmlRacEnabled) {
			for (int i = 0; i < specCases.length; i++) {
				this.specCases[i].generateCheckOfPrecondition(methodScope, methodDeclaration, codeStream);
			}
			for (int i = 0; i < redundantSpecCases.length; i++) {
				this.redundantSpecCases[i].generateCheckOfPrecondition(methodScope, methodDeclaration, codeStream);
			}
		}
	}

	public void generateCheckOfEnsures(BlockScope currentScope, AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		if (currentScope.compilerOptions().jmlDbcEnabled && currentScope.compilerOptions().jmlRacEnabled) {
			for (int i = 0; i < specCases.length; i++) {
				this.specCases[i].generateCheckOfPostcondition(currentScope, methodDeclaration, codeStream);
			}
			for (int i = 0; i < redundantSpecCases.length; i++) {
				this.redundantSpecCases[i].generateCheckOfPostcondition(currentScope, methodDeclaration, codeStream);
			}
		}
	}


	// FIXME: make me work with more than very lightweight contracts
	public Expression getPrecondition() {
		List pres = new ArrayList();
		for (int i = 0; i < this.specCases.length; i++) {
			pres.addAll(specCases[i].getRequiresExpressions());
		}
		Expression result = JmlAstUtils.conjoin(pres);
		return result;
	}

	// FIXME: make me work with more than very lightweight contracts
	public Expression getPostcondition() {
		List pres = new ArrayList();
		for (int i = 0; i < this.specCases.length; i++) {
			pres.addAll(specCases[i].getEnsuresExpressions());
		}
		Expression result = JmlAstUtils.conjoin(pres);
		return result;
	}

}
