package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.ForStatement;
import org.eclipse.jdt.internal.compiler.ast.Statement;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;

public class JmlForStatement extends ForStatement {

	public final JmlLoopAnnotations annotations;

	public JmlForStatement(JmlLoopAnnotations annotations, Statement[] initializations, Expression condition,
			Statement[] increments, Statement action, boolean neededScope,
			int s, int e) {
		super(initializations, condition, increments, action, neededScope, s, e);
		this.annotations = annotations;
	}

	public FlowInfo analyseCode(BlockScope currentScope,
			FlowContext flowContext, FlowInfo flowInfo) {
		this.annotations.analyseCode(currentScope, flowContext, flowInfo);
		return super.analyseCode(currentScope, flowContext, flowInfo);
	}

	public void resolve(BlockScope upperScope) {
		this.annotations.resolve(upperScope);
		super.resolve(upperScope);
	}
	//TODO: implement RAC
	
	public void traverse(
			ASTVisitor visitor,
			BlockScope blockScope) {

		if (visitor.visit(this, blockScope)) {
			if (initializations != null) {
				int initializationsLength = initializations.length;
				for (int i = 0; i < initializationsLength; i++)
					initializations[i].traverse(visitor, scope);
			}

			if (condition != null)
				condition.traverse(visitor, scope);
			this.annotations.traverse(visitor, blockScope);
			if (increments != null) {
				int incrementsLength = increments.length;
				for (int i = 0; i < incrementsLength; i++)
					increments[i].traverse(visitor, scope);
			}

			if (action != null)
				action.traverse(visitor, scope);
		}
		visitor.endVisit(this, blockScope);
	
	}
}
