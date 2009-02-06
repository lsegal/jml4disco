package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.impl.BooleanConstant;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.util.Utils;

public class JmlSubtypeExpression extends Expression {
	/** A constant for the "isAssignableFrom" method selector. */
	private static final char[] IS_ASSIGNABLE_FROM = "isAssignableFrom".toCharArray(); //$NON-NLS-1$
	
	/** The left expression. */
	public final Expression left;
	
    /** The right expression. */
    public final Expression right;
    
    /**
     * Constructs a JmlSubtypeExpression with the specified parameters.
     * 
     * @param left The left expression.
     * @param right The right expression
     */
	public JmlSubtypeExpression(/*@ non_null */ Expression left, /*@ non_null */ Expression right) {
		this.left = left;
		this.right = right;
		this.sourceStart = left.sourceStart();
		this.sourceEnd = right.sourceEnd();
		Utils.assertTrue(this.sourceStart <= this.sourceEnd, "sourceStart > sourceEnd ("+this.sourceStart+" > "+this.sourceEnd+")"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
		constant = Constant.NotAConstant;
		resolvedType = TypeBinding.BOOLEAN;
	}
	
	/** {@inheritDoc} */
	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		flowInfo = left.analyseCode(currentScope, flowContext, flowInfo);
		flowInfo = right.analyseCode(currentScope, flowContext, flowInfo);
		
		return flowInfo;
	}

	/** {@inheritDoc} */
	public StringBuffer printExpression(int indent, StringBuffer output) {
		left.printExpression(0, output);
		output.append(" <: "); //$NON-NLS-1$
		right.printExpression(0, output);
		return output;
	}

	/** {@inheritDoc} */
	public TypeBinding resolveType(BlockScope upperScope) {
		// both left and right must be assignable to java.lang.Class
		TypeBinding javaLangClass = upperScope.getJavaLangClass();
		TypeBinding leftType = left.resolveType(upperScope);
		if (leftType == null || leftType == TypeBinding.NULL) {
			upperScope.problemReporter().typeMismatchError(TypeBinding.NULL, javaLangClass, left, null);
		} else if (!leftType.erasure().isCompatibleWith(javaLangClass)) {
			upperScope.problemReporter().typeMismatchError(leftType, javaLangClass, left, null);
		}
		TypeBinding rightType = right.resolveType(upperScope);
		if (rightType == null || rightType == TypeBinding.NULL) {
			upperScope.problemReporter().typeMismatchError(TypeBinding.NULL, javaLangClass, right, null);
		} else if (!rightType.erasure().isCompatibleWith(javaLangClass)) {
			upperScope.problemReporter().typeMismatchError(rightType, javaLangClass, right, null);
		}

		// a subtype expression is always Boolean, which was set in the constructor
		return resolvedType;
	}
	
	/** {@inheritDoc} */
	public void generateCode(BlockScope currentScope, CodeStream codeStream, boolean valueRequired) {
		// left <: right means the same thing as right.isAssignableFrom(left)
		
		if (left.resolvedType instanceof ReferenceBinding) {
			ReferenceBinding rb = (ReferenceBinding) left.resolvedType;
			MethodBinding[] methods = rb.getMethods(IS_ASSIGNABLE_FROM);
			MethodBinding iafMethod = null;
			
			if (methods.length == 1) {
				iafMethod = methods[0];
			} else if (valueRequired) {
				// something has gone seriously wrong, since left _must_ be of class Class, and
				// class Class is final and has only one isAssignableFrom() method... so we're just going
				// to generate a constant "false", return, and hope it gets sorted elsewhere.
				codeStream.generateConstant(BooleanConstant.fromValue(false), 0);
				return;
			}
			
			// now we have a method to call; we need to put appropriate content on the stack and call it
			// TODO: should we check for whether left is null at runtime? or do we assume that an NPE is
			// a reasonable runtime consequence? 
			
			right.generateCode(currentScope, codeStream, valueRequired);
			left.generateCode(currentScope, codeStream, valueRequired);
			if (valueRequired) {
				codeStream.invokevirtual(iafMethod);
			}
		} else if (valueRequired) {
			// if left isn't a reference binding, we can't call anything on it, so we have no choice
			// but to generate a constant "false" and hope it gets sorted elsewhere.
			codeStream.generateConstant(BooleanConstant.fromValue(false), 0);
		}
	}
}
