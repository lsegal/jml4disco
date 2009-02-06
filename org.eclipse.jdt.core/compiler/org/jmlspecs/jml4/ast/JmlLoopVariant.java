package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.SingleTypeReference;
import org.eclipse.jdt.internal.compiler.codegen.BranchLabel;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

public class JmlLoopVariant extends JmlClause {

	public final Expression expr;
	private /*nullable*/ LocalDeclaration variantLocal;
	private static int varCount = 0;

	public JmlLoopVariant(String clauseKeyword, boolean isRedundant,
			Expression expr) {
		super(clauseKeyword, isRedundant);
		this.expr = expr;
	}

	public void analyseCode(BlockScope scope, FlowContext context,
			FlowInfo flowInfo) {
		this.expr.analyseCode(scope, context, flowInfo);
		flowInfo.markAsDefinitelyAssigned(this.variantLocal.binding);
		this.variantLocal.binding.useFlag = LocalVariableBinding.USED;
	}

	public void resolve(BlockScope scope) {
		TypeBinding type = this.expr.resolveTypeExpecting(scope, TypeBinding.INT);
		this.expr.computeConversion(scope, type, type);	
		createLocalForStore(scope);
		scope.addLocalVariable(this.variantLocal.binding);
		this.variantLocal.binding.recordInitializationStartPC(0);
	}
	//@ ensures  this.variantLocal != null && this.variantLocal.binding != null;
	private void createLocalForStore(BlockScope scope) {
		JmlLocalDeclaration local = new JmlLocalDeclaration(("jml$var_"+(varCount ++)).toCharArray(), 0, 0); //$NON-NLS-1$
		local.type = new SingleTypeReference("int".toCharArray(), 0); //$NON-NLS-1$
		local.type.resolve(scope);
		local.resolve(scope);
		final TypeBinding resolvedType = (local.type == null) ? null : local.type.resolvedType;
		local.binding = new LocalVariableBinding(local, resolvedType, 0, false);
		local.bits |= ASTNode.IsLocalDeclarationReachable | ASTNode.FirstAssignmentToLocal ; // only set if actually reached
		this.variantLocal = local;
	} 

	public void generateCheck(BlockScope currentScope,
			AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		throw new RuntimeException("shouldn't be called"); //$NON-NLS-1$
	}
	public void generateVariantCheck(BlockScope currentScope, CodeStream codeStream) {
		BranchLabel aLabel = new BranchLabel(codeStream);
		BranchLabel nextLabel = new BranchLabel(codeStream);

		// gen variant
		this.expr.generateCode(currentScope, codeStream, true);

		// dup dup
		codeStream.dup();
		codeStream.dup();
		// stack has |-  ... new new new

		// load jml$variant
		codeStream.load(variantLocal.binding);
		// stack has |-  ... new new new old

		// compare if < goto A
		codeStream.if_icmplt(aLabel);
		
		// pop pop
		codeStream.pop();
		codeStream.pop();

		// throw
		String msg1 = "loop variant did not decrease ('"+(this.expr.toString())+"')";  //$NON-NLS-1$//$NON-NLS-2$
		codeStream.newClassFromName(JML_RUNTIME_EXCEPTION, msg1);
		codeStream.athrow();

		// A:
		aLabel.place();
		
		// comp >= 0 goto OK
		codeStream.ifge(nextLabel);
		
		// pop
		codeStream.pop();

		// throw
		String msg2 = "loop variant negative ('"+(this.expr.toString())+"')";  //$NON-NLS-1$//$NON-NLS-2$
		codeStream.newClassFromName(JML_RUNTIME_EXCEPTION, msg2);
		codeStream.athrow();

		nextLabel.place();
		codeStream.store(variantLocal.binding, false);
	}
	
	public void generateAndStore(BlockScope currentScope, CodeStream codeStream) {
		this.expr.generateCode(currentScope, codeStream, true);
		codeStream.store(variantLocal.binding, false);
	}

	public void initStore(BlockScope currentScope, CodeStream codeStream) {
		this.expr.generateCode(currentScope, codeStream, true);
		codeStream.store(variantLocal.binding, false);
	}
	
	public void traverse(ASTVisitor visitor, BlockScope scope) {
		if(visitor.visit(this, scope)) {
			if(this.expr != null)
				this.expr.traverse(visitor, scope);
			super.traverse(visitor, scope);
		}
		visitor.endVisit(this, scope);
	}

	public StringBuffer print(int indent, StringBuffer output) {
		printIndent(indent, output).append(this.clauseKeyword + SPACE);
		this.expr.print(0, output);
		return output.append(SEMICOLON);
	}

}
