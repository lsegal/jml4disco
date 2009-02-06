package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlSignalsClause extends JmlClause {

	public final /*@nullable*/ String identifier;
	public final TypeReference thrownType;
	public final boolean explicitlyNotSpecified;
	
	public JmlSignalsClause(String clauseKeyword,
			boolean isRedundant, TypeReference thrownType,
			String identifier, Expression pred) {
		super(clauseKeyword, isRedundant, pred);
		this.identifier = identifier;
		this.thrownType = thrownType;
		this.explicitlyNotSpecified = false;
	}

	public JmlSignalsClause(String clauseKeyword,
			boolean isRedundant, TypeReference thrownType,
			Expression pred) {
		super(clauseKeyword, isRedundant, pred);
		this.identifier = null;
		this.thrownType = thrownType;
		this.explicitlyNotSpecified = false;
	}
	
	public JmlSignalsClause(String clauseKeyword,
			boolean isRedundant, TypeReference thrownType,
			boolean explicitlyNotSpecified) {
		super(clauseKeyword, isRedundant);
		this.identifier = null;
		this.thrownType = thrownType;
		this.explicitlyNotSpecified = explicitlyNotSpecified;
	}
	
	public JmlSignalsClause(String clauseKeyword,
			boolean isRedundant, TypeReference thrownType,
			String identifier, boolean explicitlyNotSpecified) {
		super(clauseKeyword, isRedundant);
		this.identifier = identifier;
		this.thrownType = thrownType;
		this.explicitlyNotSpecified = explicitlyNotSpecified;
	}

	public void generateCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		// Nothing to do
	}

	public void analyseCode(BlockScope scope, FlowContext context, FlowInfo flowInfo) {
		if (hasPred()) {
			super.analyseCode(scope, context, flowInfo);
		}
	}

	public StringBuffer print(int indent, StringBuffer output) {
		// TODO Auto-generated method stub
		return super.print(indent, output);
	}

	public void resolve(BlockScope scope) {
		TypeBinding throwable = scope.getJavaLangThrowable();
		this.thrownType.resolveTypeExpecting(scope, throwable);
		if (hasPred()) {
			super.resolve(scope);
		}
	}

}
