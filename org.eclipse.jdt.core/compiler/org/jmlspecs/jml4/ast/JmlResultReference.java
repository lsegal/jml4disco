package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.impl.ReferenceContext;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;


public class JmlResultReference extends Expression {

	// FIXME: [chalin] shouldn't this be a subtype of Reference?
	
	public JmlResultReference(int sourceStart, int sourceEnd) {
		super();
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
		this.constant = Constant.NotAConstant;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		return output.append("\\result"); //$NON-NLS-1$
	}

	public StringBuffer printExpression(int indent, StringBuffer output) {
		return this.print(indent, output);
	}

	public TypeBinding resolveType(BlockScope scope) {
		LocalVariableBinding resultBinding = getResultBinding(scope);
		return resultBinding == null ? TypeBinding.VOID : resultBinding.type;
	}

	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo, boolean valueRequired) {
		LocalVariableBinding binding = getResultBinding(currentScope);
		flowInfo.isDefinitelyAssigned(binding);
		return flowInfo;
	}

	private /*@nullable*/ LocalVariableBinding getResultBinding(BlockScope currentScope) {
		ReferenceContext referenceContext = currentScope.methodScope().referenceContext;
		JmlMethodDeclaration jmlMethodDeclaration = ((JmlMethodDeclaration)referenceContext);
		JmlLocalDeclaration localDecl = jmlMethodDeclaration.resultValue;
		return localDecl== null ? null : localDecl.binding;
	}

	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		return this.analyseCode(currentScope, flowContext, flowInfo, true);
	}

	public void generateCode(BlockScope currentScope, CodeStream codeStream, boolean valueRequired) {
		final LocalVariableBinding resultBinding = getResultBinding(currentScope);
		codeStream.load(resultBinding);
	}
	public void traverse(ASTVisitor visitor, BlockScope scope) {
		visitor.visit(this, scope);
		visitor.endVisit(this, scope);
	}
}