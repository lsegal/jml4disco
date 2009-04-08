package org.jmlspecs.jml4.ast;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;

public class JmlSpecCaseBody extends ASTNode {

	public static final JmlLocalDeclaration NoLocalDeclarations[] = new JmlLocalDeclaration[0];

	public final /*@nullable*/ JmlSpecCaseHeader header;
	public final /*@nullable*/ JmlSpecCaseRest rest;
	private JmlLocalDeclaration[] forallVars;
	private JmlLocalDeclaration[] oldVars;

	//@ requires header != null ^ rest != null;
	public JmlSpecCaseBody(JmlLocalDeclaration[] forallVars, JmlLocalDeclaration[] oldVars, JmlSpecCaseHeader header, JmlSpecCaseRest rest) {
		this.forallVars = forallVars;
		this.oldVars = oldVars;
		this.header = header;
		this.rest = rest;
		
		this.sourceStart = header != null ? header.sourceStart : rest.sourceStart;
		this.sourceEnd = rest != null ? rest.sourceEnd : header.sourceStart;
	}

	// FIXME: add resolution, analysis and print support for forallVars and oldVars.
	
	public StringBuffer print(int indent, StringBuffer output) {
		if (this.header != null)
			output = this.header.print(indent, output);
		if (this.rest != null)
			output = this.rest.print(indent, output);
		return output;
	}
	public void analysePrecondition(MethodScope scope, FlowContext methodContext, FlowInfo flowInfo) {
		if (this.header != null)
			this.header.analysePrecondition(scope, methodContext, flowInfo);
	}
	public void analysePostcondition(MethodScope scope, FlowContext methodContext, FlowInfo flowInfo) {
		if (this.rest != null)
			this.rest.analysePostcondition(scope, methodContext, flowInfo);
	}
	public void generateCheckOfPrecondition(MethodScope methodScope, AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		if (this.header != null)
			this.header.generateCheckOfPrecondition(methodScope, methodDeclaration, codeStream);
	}
	public void generateCheckOfPostcondition(BlockScope currentScope, AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		if (this.rest != null)
			this.rest.generateCheckOfPostcondition(currentScope, methodDeclaration, codeStream);
	}
	public void resolve(MethodScope scope) {
		if (this.header != null)
			this.header.resolve(scope);
		if (this.rest != null)
			this.rest.resolve(scope);
	}
	public List/*<Expression>*/ getRequiresExpressions() {
		List/*<Expression>*/ result = new ArrayList/*<Expression>*/();
		if (this.header != null)
			result.addAll(this.header.getRequiresExpressions());
		return result;
	}
	public List/*<Expression>*/ getEnsuresExpressions() {
		List/*<Expression>*/ result = new ArrayList/*<Expression>*/();
		if (this.rest != null)
			result.addAll(this.rest.getEnsuresExpressions());
		return result;
	}
	public JmlLocalDeclaration[] getForallVars() {
		return forallVars;
	}

	public JmlLocalDeclaration[] getOldVars() {
		return oldVars;
	}
}
