package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.SingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.Statement;
import org.eclipse.jdt.internal.compiler.ast.WhileStatement;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlWhileStatement extends WhileStatement {

	public final JmlLoopAnnotations annotations;
	private JmlLocalDeclaration firstTimeLocal;
	private static int firstTimeThroughCount = 0;

	public JmlWhileStatement(JmlLoopAnnotations annotations, Expression condition, Statement action, int s, int e) {
		super(condition, action, s, e);
		this.annotations = annotations;
	}

	public FlowInfo analyseCode(BlockScope currentScope,
			FlowContext flowContext, FlowInfo flowInfo) {
		flowInfo.markAsDefinitelyAssigned(firstTimeLocal.binding);
		firstTimeLocal.binding.useFlag = LocalVariableBinding.USED;
		this.annotations.analyseCode(currentScope, flowContext, flowInfo);
		return super.analyseCode(currentScope, flowContext, flowInfo);
	}

	public void resolve(BlockScope scope) {
		this.annotations.resolve(scope);
		
		createLocalForFirstTime(scope);
		scope.addLocalVariable(this.firstTimeLocal.binding);
		this.firstTimeLocal.binding.recordInitializationStartPC(0);
		super.resolve(scope);
	}

	//@ ensures  this.firstTimeLocal != null && this.firstTimeLocal.binding != null;
	private void createLocalForFirstTime(BlockScope scope) {
		JmlLocalDeclaration firstTime = new JmlLocalDeclaration(("jml$firstTimeThrough_"+(firstTimeThroughCount++)).toCharArray(), 0, 0); //$NON-NLS-1$
		firstTime.type = new SingleTypeReference("int".toCharArray(), 0); //$NON-NLS-1$
		firstTime.resolve(scope);
		final TypeBinding resolvedType = (firstTime.type == null) ? null : firstTime.type.resolvedType;
		firstTime.binding = new LocalVariableBinding(firstTime, resolvedType, 0, false);
		firstTime.bits |= ASTNode.IsLocalDeclarationReachable | ASTNode.FirstAssignmentToLocal ; // only set if actually reached
		this.firstTimeLocal= firstTime;
	} 

	protected void checkLoopInvariant(BlockScope currentScope, CodeStream codeStream) {
		if (!racIsEnabled(currentScope))
			return;
		this.annotations.checkLoopInvariant(currentScope, codeStream);
	}

	protected void emitCodeBeforeContinueLabel(BlockScope currentScope, CodeStream codeStream) { 
		if (!racIsEnabled(currentScope))
			return;
		codeStream.generateInlinedValue(1);
		codeStream.store(this.firstTimeLocal.binding, false);
		this.annotations.initVariantStore(currentScope, codeStream);
	}

	protected void checkLoopVariant(BlockScope currentScope, CodeStream codeStream) { 
		if (!racIsEnabled(currentScope))
			return;
		this.annotations.checkLoopVariant(currentScope, codeStream, this.firstTimeLocal.binding);
	}

	private boolean racIsEnabled(BlockScope currentScope) {
		return currentScope.compilerOptions() != null 
				&& currentScope.compilerOptions().jmlEnabled
				&& currentScope.compilerOptions().jmlRacEnabled;
	}

	public void traverse(ASTVisitor visitor, BlockScope blockScope) {
		if (visitor.visit(this, blockScope)) {
			this.condition.traverse(visitor, blockScope);
			this.annotations.traverse(visitor, blockScope);
			if (this.action != null)
				this.action.traverse(visitor, blockScope);
		}
		visitor.endVisit(this, blockScope);
	}
	
	public StringBuffer printStatement(int tab, StringBuffer output) {
//		if (JmlAstUtils.useSupersToStringMethod)
//			return super.printStatement(tab, output);
		output = this.annotations.print(tab, output);
		return super.printStatement(tab, output);
	}
}
