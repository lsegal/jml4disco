package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Annotation;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ExtraCompilerModifiers;
import org.jmlspecs.jml4.compiler.parser.JmlIdentifier;

public abstract class JmlTypeBodyDeclaration extends JmlClause {
	
	// The following fields are not set at construction time, but a little later:
	protected int modifiers = 0;
	protected Annotation[] jmlAnnotations = new Annotation[0];
	public int modifiersSourceStart = -1;
	//@ private boolean modifiersHasBeenSet = false;

	// FIXME: properly handle static clauses.
	protected boolean isStatic = false;
	
	public JmlTypeBodyDeclaration(JmlIdentifier clauseKeyword) {
		super(clauseKeyword);
	}
	
	public JmlTypeBodyDeclaration(JmlIdentifier clauseKeyword, Expression pred) {
		super(clauseKeyword, pred);
	}

	public abstract void resolve(BlockScope staticInitializerScope, BlockScope initializerScope);
	
	// analyseCode should call checkModifiers.
	public abstract FlowInfo analyseCode(BlockScope staticInitializerScope, BlockScope initializerScope, FlowContext context, FlowInfo flowInfo);
	// public abstract void generateCheck(BlockScope currentScope, AbstractMethodDeclaration methodDecl, CodeStream codeStream, String msg);

	protected void checkModifiers(BlockScope scope, int validModifiers, String validModifierList) {
		checkVisibilityModifiers(scope);
		if ((modifiers & validModifiers) != modifiers) {
			scope.problemReporter().invalidModifier("member declaration", clauseKeyword(), validModifierList, this); //$NON-NLS-1$
		}
	}

	protected void checkVisibilityModifiers(BlockScope scope) {
		final int visibility = modifiers & ExtraCompilerModifiers.AccVisibilityMASK;
		if (visibility != 0 && visibility != ClassFileConstants.AccPrivate && visibility != ClassFileConstants.AccProtected && visibility != ClassFileConstants.AccPublic) {
			scope.problemReporter().duplicateModifier("member declaration", clauseKeyword(), this); //$NON-NLS-1$
		}
	}
	
	//@ requires ! modifiersHasBeenSet;
	//@ ensures    modifiersHasBeenSet;
	//@ ensures this.modifiers == modifiers;
	public void setModifers(int modifers, int modifiersSourceStart) {
		this.modifiers = modifers;
		this.modifiersSourceStart = modifiersSourceStart;
		// this.modifiersHasBeenSet = true;
	}
	
	public void setJmlAnnotations(Annotation[] annotations) {
		this.jmlAnnotations = annotations;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		// FIXME: also need to print the modifiers
		return super.print(indent, output);
	}
	
}
