/**
 * $Id: Nullity.java,v 1.8 2007/06/15 20:33:19 chalin Exp $	
 * // FIXME: add JavaDocs to the jml4 files
 * 
 */
package org.jmlspecs.jml4.nonnull;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.flow.LoopingFlowContext;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.TagBits;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeIds;
import org.jmlspecs.jml4.ast.JmlTypeReference;
import org.jmlspecs.jml4.util.Logger;

public class Nullity {
	private static final boolean DEBUG = false;
	private final String name;

	public static final Nullity _default = new Nullity("default-nullity"),  //$NON-NLS-1$
	                            non_null = new Nullity("non_null"),         //$NON-NLS-1$
	                            mono_non_null = new Nullity("mono_non_null"),         //$NON-NLS-1$
	                            nullable = new Nullity("nullable"),         //$NON-NLS-1$
                                non_null_by_default = new Nullity("non_null_by_default"),  //$NON-NLS-1$
                                nullable_by_default = new Nullity("nullable_by_default");  //$NON-NLS-1$

    private Nullity(String name) {this.name=name;}
	public static Nullity fromString(String s) {
		if (s.equals("non_null_by_default") || s.equals(non_null_by_default.toString())) return non_null_by_default; //$NON-NLS-1$
		if (s.equals("nullable") || s.equals(nullable.toString())) return nullable; //$NON-NLS-1$
		if (s.equals("non_null") || s.equals(non_null.toString())) return non_null; //$NON-NLS-1$
		if (s.equals("nullable_by_default") || s.equals(nullable_by_default.toString())) return nullable_by_default; //$NON-NLS-1$
		return _default;
	}
	public String toString() {return this.name;}
	public boolean isNon_null() { return this == non_null || this == non_null_by_default; }
	public boolean isNullable() { return this == nullable || this == nullable_by_default; }
	public boolean isMono_non_null() { return this == mono_non_null; }
	public boolean isNon_nullByDefault() { return this == non_null_by_default; }
	public boolean isNullableByDefault() { return this == nullable_by_default; }
	public boolean hasExplicitNullity()  { return this == non_null || this == mono_non_null || this == nullable; }
	public boolean hasDefaultNullity()   { return ! hasExplicitNullity(); }

	public static boolean isAssignable(TypeReference typeReference, Expression expression, BlockScope scope, FlowContext flowContext, FlowInfo flowInfo) {
	// result == lhs is not declared non null
	//        or rhs is delcared non null
	//        or rhs is a local (or param) that flowInfo says is currently non-null
		if (typeReference instanceof JmlTypeReference) {
			Nullity nullity = ((JmlTypeReference)typeReference).getNullity();
			boolean leftIsDeclaredNonNull = nullity.isNon_null();
			boolean leftIsDeclaredMono    = nullity.isMono_non_null();
if (DEBUG) Logger.println("isAssignable leftIsDeclaredNonNull = "+leftIsDeclaredNonNull);		 //$NON-NLS-1$
			if (!leftIsDeclaredNonNull && !leftIsDeclaredMono) {
				return true;
			}
		} else {
if (DEBUG) Logger.println("Nullity.isAssignable(): typeReference is not a JmlTypeReference. it is a '"+typeReference.getClass().toString()+"'");		 //$NON-NLS-1$ //$NON-NLS-2$
			return true;
		}
		if (expression.isDeclaredNonNull()) {
			return true;
		}
		if (expression.nullStatus(flowInfo) == FlowInfo.NON_NULL) {
			return true;
		}
		if (expression.localVariableBinding() == null) {
			return false;
		}
		preparePossibleUnknowns(expression, scope, flowContext, flowInfo);
if (DEBUG) Logger.println("expression.class                = "+expression.getClass());		 //$NON-NLS-1$
if (DEBUG) Logger.println("expression.isDeclaredNonNull()  = "+expression.isDeclaredNonNull());		 //$NON-NLS-1$
if (DEBUG) Logger.println("expression.nullStatus(flowInfo) = "+expression.nullStatus(flowInfo));		 //$NON-NLS-1$
if (DEBUG) Logger.println("   FlowInfo.NON_NULL            = "+FlowInfo.NON_NULL);			 //$NON-NLS-1$
if (DEBUG) Logger.println("   FlowInfo.NULL                = "+FlowInfo.NULL);		 //$NON-NLS-1$
if (DEBUG) Logger.println("   FlowInfo.UNKNOWN             = "+FlowInfo.UNKNOWN);		 //$NON-NLS-1$
		boolean rightIsNonNull = expression.nullStatus(flowInfo) == FlowInfo.NON_NULL;
if (DEBUG) Logger.println("rightIsNonNull                  = "+rightIsNonNull);		 //$NON-NLS-1$
		return rightIsNonNull;
	}
	public static void preparePossibleUnknowns(Expression exp, BlockScope scope, FlowContext flowContext, FlowInfo flowInfo) {
		// we only need to do this because the bodies of loops
		// (including their conditions, as well as inits and incs for "for loops") 
		// are processed without nullity information. 
		// (see e.g., the line
        //  >> "FlowInfo condInfo =	flowInfo.nullInfoLessUnconditionalCopy();" 
		// in WhileStatement.analyseCode())

		if (! (flowContext instanceof LoopingFlowContext))
			return;
		// the following code is taken from Expression.checkNPE()

		LocalVariableBinding local = exp.localVariableBinding();
		if (local != null && 
				(local.type.tagBits & TagBits.IsBaseType) == 0) {
			if ((exp.bits & ASTNode.IsNonNull) == 0) {
				if (!(scope.compilerOptions().useNonNullTypeSystem()
						 && exp.isDeclaredNonNull())) {
				flowContext.recordUsingNullReference(scope, local, exp, 
						FlowContext.MAY_NULL, flowInfo);
				}
			}
			flowInfo.markAsComparedEqualToNonNull(local); 
				// from thereon it is set
			if (flowContext.initsOnFinally != null) {
				flowContext.initsOnFinally.markAsComparedEqualToNonNull(local); 
			}
		}
	}
	public static boolean isPrimitiveType(TypeBinding binding) {
		return binding != null 
		    && (binding.isNumericType() 
		    ||  binding.id ==TypeIds.T_void 
		    ||  binding.id ==TypeIds.T_boolean);
	}
}
