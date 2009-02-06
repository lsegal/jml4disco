package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

public class JmlAssignableClause extends JmlClause {

	public final JmlStoreRef[] storeRefs;
	//@ invariant storeRefs.length >= 1;

	//@ requires storeRefs.length >= 1;
	//@ ensures  this.clauseKeyword == clauseKeyword;
	//@ ensures  this.storeRefs == storeRefs;
	public JmlAssignableClause(String clauseKeyword, boolean isRedundant, JmlStoreRef[] storeRefs) {
		super(clauseKeyword, isRedundant);
		this.storeRefs = storeRefs;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		output.append(this.clauseKeyword + " "); //$NON-NLS-1$
		storeRefs[0].print(indent, output);
		for (int i = 1; i < storeRefs.length; i++) {
			output.append(", "); //$NON-NLS-1$
			storeRefs[i].print(indent, output);
		}
		return output.append(";"); //$NON-NLS-1$
	}

	public void resolve(BlockScope scope) {
		for (int i = 0; i < storeRefs.length; i++) {
			storeRefs[i].resolve(scope);
		}
	}

	public void analyseCode(BlockScope scope, FlowContext methodContext, FlowInfo flowInfo) {
		for (int i = 0; i < storeRefs.length; i++) {
			storeRefs[i].analyseCode(scope, methodContext, flowInfo);
		}
		// TODO: Do we want to do checks to see that there are no duplicates?
	}

	public void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDeclaration, CodeStream codeStream) {
		/* empty, since we don't do runtime checks of assignable clauses */
	}

}
