package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.lookup.ArrayBinding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeVariableBinding;

public class JmlElemtypeExpression extends JmlUnaryExpression {
	
	private /*@nullable*/ TypeBinding targetType;

	public JmlElemtypeExpression(Expression expression, int operator) {
		super(expression, operator);
	}
	
	public /*@nullable*/ TypeBinding resolveType(BlockScope scope) {
		super.resolveType(scope); // value from super ignored
		ReferenceBinding classType = scope.getJavaLangClass();
		if (expression.resolvedType == null) {
			return null;
		}
		if (! (expression.resolvedType.isClass())) {
			scope.problemReporter().typeMismatchError(expression.resolvedType, classType, this, null);
			return null;
		}
		TypeBinding expType;
		if (expression instanceof JmlTypeExpression) {
			expType = ((JmlTypeExpression) expression).targetType(); 
		} else if (expression instanceof JmlTypeofExpression) {
			expType = ((JmlTypeofExpression) expression).targetType();
		} else {
			// expression.resolvedType must be of type Class.
			// e.g., \elemtype(c) where Class<Integer[]> c = Integer[].class
			// TODO: add an assert of the above comment
			targetType = null; // pending; perhaps better to analyze expType.
			this.resolvedType = scope.environment().convertToRawType(expression.resolvedType, false);
			return this.resolvedType;
		}
		if (expType == null)
			return null;
		
		if (expType.isArrayType()) {
			ArrayBinding arrayBinding = (ArrayBinding) expType;
			TypeBinding leafComponentType = arrayBinding.leafComponentType;							
			if (leafComponentType == TypeBinding.VOID) {
				// this branch looks unreachable.
				scope.problemReporter().cannotAllocateVoidArray(this);
				return null;
			} else if (leafComponentType.isTypeVariable()) {
				scope.problemReporter().illegalClassLiteralForTypeVariable((TypeVariableBinding)leafComponentType, this);
			} else {
				if (arrayBinding.dimensions < 2) {
					targetType = leafComponentType;
				} else {
					ArrayBinding elmtType = scope.environment().createArrayType(leafComponentType, arrayBinding.dimensions-1);
					targetType = elmtType;
				}									
			}
			if (classType.isGenericType() && targetType != null) {
				// Integer.class --> Class<Integer>, perform boxing of base types (int.class --> Class<Integer>)
				TypeBinding boxedType = null;
				if (targetType.id == T_void) {
					boxedType = scope.environment().getResolvedType(JAVA_LANG_VOID, scope);
				} else {
					boxedType = scope.boxing(targetType);
				}
				this.resolvedType = scope.environment().createParameterizedType(classType, new TypeBinding[]{ boxedType }, null/*not a member*/);
			} else {
				this.resolvedType = classType;
			}
			return this.resolvedType;
		} else {
			targetType = null;
			this.resolvedType = scope.environment().convertToRawType(classType, false);
			return this.resolvedType;
		}
	}

	public TypeBinding targetType() {
		return this.targetType;
	}

}
