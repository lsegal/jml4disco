/*******************************************************************************
 * Copyright (c) 2000, 2008 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.internal.codeassist.select;

/*
 * Selection node build by the parser in any case it was intending to
 * reduce an allocation expression containing the cursor.
 * If the allocation expression is not qualified, the enclosingInstance field
 * is null.
 * e.g.
 *
 *	class X {
 *    void foo() {
 *      new [start]Bar[end](1, 2)
 *    }
 *  }
 *
 *	---> class X {
 *         void foo() {
 *           <SelectOnAllocationExpression:new Bar(1, 2)>
 *         }
 *       }
 *
 */

import org.eclipse.jdt.internal.compiler.ast.ConstructorDeclaration;
import org.eclipse.jdt.internal.compiler.ast.QualifiedAllocationExpression;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.LocalTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.ProblemReasons;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
 
public class SelectionOnQualifiedAllocationExpression extends QualifiedAllocationExpression {

	public SelectionOnQualifiedAllocationExpression() {
		// constructor without argument
	}
	
	public SelectionOnQualifiedAllocationExpression(TypeDeclaration anonymous) {
		super(anonymous);
	}
	
	public StringBuffer printExpression(int indent, StringBuffer output) {
		if (this.enclosingInstance == null)
			output.append("<SelectOnAllocationExpression:");  //$NON-NLS-1$
		else 
			output.append("<SelectOnQualifiedAllocationExpression:"); //$NON-NLS-1$

		return super.printExpression(indent, output).append('>'); 
	}
	
	public TypeBinding resolveType(BlockScope scope) {
		super.resolveType(scope);
	
		if (binding == null) {
			throw new SelectionNodeFound();
		}
		
		// tolerate some error cases
		if (!binding.isValidBinding()) {
			switch (binding.problemId()) {
				case ProblemReasons.NotVisible:
					// visibility is ignored
					break;
				case ProblemReasons.NotFound:
					if (resolvedType != null && resolvedType.isValidBinding()) {
						throw new SelectionNodeFound(resolvedType);
					}
					throw new SelectionNodeFound();
				default:
					throw new SelectionNodeFound();
			}
		}
		
		if (anonymousType == null)
			throw new SelectionNodeFound(binding);
	
		// if selecting a type for an anonymous type creation, we have to
		// find its target super constructor (if extending a class) or its target 
		// super interface (if extending an interface)
		if (anonymousType.binding != null) {
			LocalTypeBinding localType = (LocalTypeBinding) anonymousType.binding;
			if (localType.superInterfaces == Binding.NO_SUPERINTERFACES) {
				// find the constructor binding inside the super constructor call
				ConstructorDeclaration constructor = (ConstructorDeclaration) anonymousType.declarationOf(binding.original());
				if (constructor != null) {
					throw new SelectionNodeFound(constructor.constructorCall.binding);
				}
				throw new SelectionNodeFound(binding);
			}
			// open on the only super interface
			throw new SelectionNodeFound(localType.superInterfaces[0]);
		} else {
			if (this.resolvedType.isInterface()) {
				throw new SelectionNodeFound(resolvedType);
			}
			throw new SelectionNodeFound(binding);
		}
	}
}
