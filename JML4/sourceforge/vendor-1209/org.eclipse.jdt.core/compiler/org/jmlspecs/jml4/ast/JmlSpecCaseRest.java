package org.jmlspecs.jml4.ast;

import java.util.List;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;

public abstract class JmlSpecCaseRest extends ASTNode {

	public abstract void resolve(MethodScope scope);

	public abstract void generateCheckOfPostcondition(BlockScope currentScope,
			AbstractMethodDeclaration methodDeclaration, CodeStream codeStream);

	public abstract void analysePostcondition(MethodScope scope, FlowContext methodContext,
			FlowInfo flowInfo);

	public abstract List/*<Expression>*/ getEnsuresExpressions();

}