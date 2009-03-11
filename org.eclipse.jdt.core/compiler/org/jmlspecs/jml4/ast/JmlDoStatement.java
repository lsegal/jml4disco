package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.DoStatement;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.Statement;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

public class JmlDoStatement extends DoStatement {

	public final JmlLoopAnnotations annotations;

	public JmlDoStatement(JmlLoopAnnotations annotations, Expression condition, Statement action,
			int sourceStart, int sourceEnd) {
		super(condition, action, sourceStart, sourceEnd);
		this.annotations = annotations;
	}
	public FlowInfo analyseCode(BlockScope currentScope,
			FlowContext flowContext, FlowInfo flowInfo) {
		this.annotations.analyseCode(currentScope, flowContext, flowInfo);
		return super.analyseCode(currentScope, flowContext, flowInfo);
	}

	public void resolve(BlockScope scope) {
		this.annotations.resolve(scope);
		super.resolve(scope);
	}

	//TODO: implement RAC
	public void traverse(ASTVisitor visitor, BlockScope scope) {
		if (visitor.visit(this, scope)) {
			this.annotations.traverse(visitor, scope);
			if (this.action != null) {
				this.action.traverse(visitor, scope);
			}
			this.condition.traverse(visitor, scope);
		}
		visitor.endVisit(this, scope);
	}	
}
