package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.codegen.BranchLabel;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;

public class JmlLoopAnnotations extends JmlAstNode {

	public final JmlLoopInvariant[] invariants;
	public final JmlLoopVariant[]   variants;
	private static final JmlLoopInvariant[] emptyInvariants = new JmlLoopInvariant[0];
	private static final JmlLoopVariant[]   emptyVariants = new JmlLoopVariant[0];
	
	public JmlLoopAnnotations(JmlLoopInvariant[] invariants) {
		this.invariants = invariants;
		this.variants = emptyVariants;
	}

	public JmlLoopAnnotations(JmlLoopVariant[] variants) {
		this.invariants = emptyInvariants;
		this.variants = variants;
	}

	public JmlLoopAnnotations(JmlLoopInvariant[] invariants, JmlLoopVariant[] variants) {
		this.invariants = invariants;
		this.variants = variants;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		for (int i = 0; i < this.invariants.length; i++) {
			this.invariants[i].print(indent, output);
			output.append('\n'); 
		}
		for (int i = 0; i < this.variants.length; i++) {
			this.variants[i].print(indent, output);
			output.append('\n'); 
		}
		return output;
	}

	public void checkLoopInvariant(BlockScope currentScope,
			CodeStream codeStream) {
		for (int i=0; i<this.invariants.length; i++) {
			this.invariants[i].generateCheck(currentScope, codeStream);
		}
	}
	public void checkLoopVariant(BlockScope currentScope,
			CodeStream codeStream, LocalVariableBinding firstTimeBinding) {
		if (this.variants.length > 0) {
			BranchLabel ftLabel = new BranchLabel(codeStream);
			BranchLabel okLabel = new BranchLabel(codeStream);

			// if jml$firstTime goto ft_label
			codeStream.load(firstTimeBinding);
			codeStream.ifne(ftLabel);

			for (int i=0; i<this.variants.length; i++) {
				this.variants[i].generateVariantCheck(currentScope, codeStream);
			}
			codeStream.goto_(okLabel);

			// ft_label:
			ftLabel.place();
			
			// store false in ft
			codeStream.generateInlinedValue(0);
			codeStream.store(firstTimeBinding, false);

			// gen variant & store in jml$variant
			for (int i=0; i<this.variants.length; i++) {
				this.variants[i].generateAndStore(currentScope, codeStream);
			}
			// ok: 
			okLabel.place();
			
		}
	}

	public void resolve(BlockScope scope) {
		for (int i=0; i<this.invariants.length; i++) {
			this.invariants[i].resolve(scope);
		}
		for (int i=0; i<this.variants.length; i++) {
			this.variants[i].resolve(scope);
		}
	}

	public void analyseCode(BlockScope currentScope, FlowContext flowContext,
			FlowInfo flowInfo) {
		for (int i=0; i<this.invariants.length; i++) {
			this.invariants[i].analyseCode(currentScope, flowContext, flowInfo);
		}
		for (int i=0; i<this.variants.length; i++) {
			this.variants[i].analyseCode(currentScope, flowContext, flowInfo);
		}
	}

	public void initVariantStore(BlockScope currentScope, CodeStream codeStream) {
		for (int i=0; i<this.variants.length; i++) {
			this.variants[i].initStore(currentScope, codeStream);
		}
	}

	public void traverse(ASTVisitor visitor, BlockScope scope) {
		if(visitor.visit(this, scope)) {
			for (int i = 0; i < this.invariants.length; i++) {
				this.invariants[i].traverse(visitor, scope);
			}
			for (int i = 0; i < this.variants.length; i++) {
				this.variants[i].traverse(visitor, scope);
			}
		}
		visitor.endVisit(this, scope);
	}
}
