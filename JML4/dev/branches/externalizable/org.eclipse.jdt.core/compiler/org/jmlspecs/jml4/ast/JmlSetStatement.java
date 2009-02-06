package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ArrayReference;
import org.eclipse.jdt.internal.compiler.ast.Assignment;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.ast.QualifiedNameReference;
import org.eclipse.jdt.internal.compiler.ast.SingleNameReference;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.ProblemFieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.ProblemReasons;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;


public class JmlSetStatement extends JmlAssignment {

	public JmlSetStatement(Assignment assgnExp, int sourceStart, int sourceEnd) {
		super(assgnExp.lhs, assgnExp.expression, sourceEnd);
		this.sourceStart = sourceStart;
	}
	
	public TypeBinding resolveType(BlockScope scope) {
		TypeBinding typBnd = super.resolveType(scope);
		if (typBnd == null) return null;
		
		checkGhost(lhs, scope);
		return typBnd;
	}
	
	private void checkGhost(Expression exp, BlockScope scope) {
		// syntax exp may be only a NameReference, a FieldReference or an ArrayReference
		// (rephrased from Assignment.resolveType)
		if (exp instanceof SingleNameReference) {
			SingleNameReference expOfNameRef = (SingleNameReference) exp;
			// check if exp is declared as a local.
			LocalVariableBinding varBnd = exp.localVariableBinding();
			if (varBnd != null) {
				if (! varBnd.isGhost) {
					scope.problemReporter().unresolvableReference(expOfNameRef, varBnd);
				}
			} else {				
				// check if exp is declared as a field.
				FieldBinding fldBnd = ((SingleNameReference) exp).fieldBinding();
				if (! fldBnd.isGhost) {
					scope.problemReporter().unresolvableReference(expOfNameRef, fldBnd);
				}
			}
		} else if (exp instanceof QualifiedNameReference) {
			QualifiedNameReference qualExp = (QualifiedNameReference) exp;
			FieldBinding lastFldBnd = qualExp.otherBindings[qualExp.otherBindings.length-1];
			if (! lastFldBnd.isGhost) {
				scope.problemReporter().unresolvableReference(qualExp,lastFldBnd);
			}
		} else if (exp instanceof FieldReference) {
			FieldReference expOfFldRef = (FieldReference) exp;
			FieldBinding bnd = expOfFldRef.binding;
			if (! bnd.isGhost) {
				expOfFldRef.binding = 
					new ProblemFieldBinding(bnd.declaringClass, bnd.name, ProblemReasons.NotVisible);
				scope.problemReporter().invalidField(expOfFldRef, bnd.type);
			}
		} else if (exp instanceof ArrayReference) {
			ArrayReference expOfArrayRef = (ArrayReference) exp;
			checkGhost(expOfArrayRef.receiver, scope);
		} 
	}
	
	public StringBuffer printExpressionNoParenthesis(int indent, StringBuffer output) {
		output.append("//@ set "); //$NON-NLS-1$
		lhs.printExpression(indent, output).append(" = "); //$NON-NLS-1$
		return expression.printExpression(0, output);
	}
}
