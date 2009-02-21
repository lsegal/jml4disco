package org.jmlspecs.jml4.util;

import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.CompoundAssignment;
import org.eclipse.jdt.internal.compiler.ast.PrefixExpression;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.jmlspecs.jml4.ast.JmlAssignment;

public class HasSideEffectsVisitor extends ASTVisitor {

	private boolean hasSideEffects = false;
	public HasSideEffectsVisitor() {
		/*empty*/
	}
	public boolean hasSideEffects() {
		return this.hasSideEffects;
	}

	public boolean visit(Assignment assignment, BlockScope scope) {
		this.hasSideEffects = true;
		return true;
	}
	public boolean visit(CompoundAssignment assignment, BlockScope scope) {
		this.hasSideEffects = true;
		return true;
	}
	public boolean visit(PostfixExpression assignment, BlockScope scope) {
		this.hasSideEffects = true;
		return true;
	}
	public boolean visit(PrefixExpression assignment, BlockScope scope) {
		this.hasSideEffects = true;
		return true;
	}
	public boolean visit(JmlAssignment assignment, BlockScope scope) {
		this.hasSideEffects = true;
		return true;
	}
}
