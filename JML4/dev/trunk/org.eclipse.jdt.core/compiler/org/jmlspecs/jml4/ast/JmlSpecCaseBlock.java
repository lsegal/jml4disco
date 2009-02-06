package org.jmlspecs.jml4.ast;

import java.util.List;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;

public class JmlSpecCaseBlock extends JmlSpecCaseRest {

	public final JmlSpecCaseBody[] bodies;

	public JmlSpecCaseBlock(JmlSpecCaseBody[] bodies) {
		this.bodies = bodies;
	}

	public void analysePostcondition(MethodScope scope,
			FlowContext methodContext, FlowInfo flowInfo) {
		// FIXME: ... simply delegating for now, but more most likely needs to be done.
		for (int i = 0; i < this.bodies.length; i++) {
			this.bodies[i].analysePostcondition(scope, methodContext, flowInfo);
		}
	}

	public void generateCheckOfPostcondition(BlockScope currentScope,
			AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		// FIXME: ... simply delegating for now, but more most likely needs to be done.
		for (int i = 0; i < this.bodies.length; i++) {
			this.bodies[i].generateCheckOfPostcondition(currentScope, methodDeclaration, codeStream);
		}
	}

	public void resolve(MethodScope scope) {
		for (int i = 0; i < this.bodies.length; i++) {
			this.bodies[i].resolve(scope);
		}
	}

	public StringBuffer print(int indent, StringBuffer output) {
		output.append("{|"); //$NON-NLS-1$
		this.bodies[0].print(indent, output);
		for (int i = 1; i < this.bodies.length; i++) {
			output.append(" also "); //$NON-NLS-1$
			this.bodies[i].print(indent, output);
		}
		output.append("|}"); //$NON-NLS-1$
		return output;
	}

	public List getEnsuresExpressions() {
		// TODO Auto-generated method stub
		return null;
	}
}
