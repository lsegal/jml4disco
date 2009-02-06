package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.core.Flags;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ExtraCompilerModifiers;

public class JmlConstraintClause extends JmlTypeBodyDeclaration {

	private static final int VALID_MODIFIERS = ExtraCompilerModifiers.AccVisibilityMASK | ClassFileConstants.AccStatic;
	private static final String VALID_MODIFIER_LIST = "public, protected, private & static"; //$NON-NLS-1$
	    
	protected boolean isStatic;
	protected boolean isStaticSet = false;

	public JmlConstraintClause(String clauseKeyword, boolean isRedundant, Expression pred) {
		super(clauseKeyword, isRedundant, pred);
	}

	public String kind() {
		return "constraint"; //$NON-NLS-1$
	}
	
	public StringBuffer print(int indent, StringBuffer output) {
		// FIXME: also need to print the modifiers
		return super.print(indent, output);
	}
	
	public void resolve(BlockScope staticInitializerScope, BlockScope initializerScope) {
		resolveBindingModifier(initializerScope);

		BlockScope scope = isStatic() ? staticInitializerScope : initializerScope;		
		super.resolve(scope);						
	}

	public FlowInfo analyseCode(BlockScope staticInitializerScope,
			BlockScope initializerScope, FlowContext context, FlowInfo flowInfo) {
		BlockScope scope = isStatic() ? staticInitializerScope : initializerScope;	
		return this.pred.analyseCode(scope, context, flowInfo);
	}

	public void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDecl, 
			CodeStream codeStream) {
		if (DEBUG) {
			generatePrintValue(currentScope, methodDecl, codeStream);
		}
		generateEvaluateAndThrowIfFalse(currentScope, codeStream);
	}

	private boolean isStatic() {
		if (!isStaticSet) {
			throw new RuntimeException("JML Error: a type must be set first."); //$NON-NLS-1$
		} else {
			return isStatic;
		}
	}
	
	/**
	 * resolves if a given type specification is whether static or instance. 
	 * @param defaultScope	default scope. currently non-static scope.
	 */
	private void resolveBindingModifier(BlockScope defaultScope) {
		checkModifiers(defaultScope, VALID_MODIFIERS, VALID_MODIFIER_LIST);			

		for (int i=0; i<this.jmlAnnotations.length; i++) {
			this.jmlAnnotations[i].resolve(defaultScope);
		}

		if (Flags.isStatic(this.modifiers) && 
				JmlModifier.isInstance(JmlModifier.getFromAnnotations(this.jmlAnnotations))) {
			defaultScope.problemReporter().invalidModifier("member declaration", this.clauseKeyword, "either static or instance and other modifiers", this);  //$NON-NLS-1$//$NON-NLS-2$
			this.isStatic = false; // default:static
			this.isStaticSet = true;
			return;
		}
		
		/*
		 * Set an invariant type if it is explicitly specified.
		 * Otherwise, decide the type according to the enclosing context.
		 * If the enclosing context is class, default type is instance, and
		 * if interface, static.
		 */
		if (JmlModifier.isInstance(JmlModifier.getFromAnnotations(this.jmlAnnotations))) {
			this.isStatic = false;
			this.isStaticSet = true;
		} else if(Flags.isStatic(this.modifiers)) {
			this.isStatic = true;
			this.isStaticSet = true;
		} else if (Flags.isInterface(this.modifiers)) {
			this.isStatic = true;
			this.isStaticSet = true;			
		} else { // enclosing context must be class.
			this.isStatic = false;
			this.isStaticSet = true;			
		}
	}
}
