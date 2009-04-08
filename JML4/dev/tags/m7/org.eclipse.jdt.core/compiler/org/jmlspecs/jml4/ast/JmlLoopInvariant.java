package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public class JmlLoopInvariant extends JmlClause {

	public JmlLoopInvariant(JmlIdentifier keyword, Expression pred) {
		super(keyword, pred);
	}

	public void generateCheck(BlockScope currentScope, CodeStream codeStream) {
		if (DEBUG) {
			generatePrintValue(currentScope, codeStream);
		}
		generateEvaluateAndThrowIfFalse(currentScope, codeStream);
	}

	public void generateCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		this.generateCheck(currentScope, codeStream);
	}

	public void traverse(ASTVisitor visitor, BlockScope scope) {
		if(visitor.visit(this, scope)) {
			super.traverse(visitor, scope);
		}
		visitor.endVisit(this, scope);
	}
}
