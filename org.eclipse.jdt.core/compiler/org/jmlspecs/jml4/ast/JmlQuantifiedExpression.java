package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlQuantifiedExpression extends Expression {
	/** The quantifier, which determines (among other things) the type of the expression. */
	public final JmlQuantifier quantifier;
	
    /** The bound variables (as LocalDeclarations). */
    public final LocalDeclaration[] boundVariables;
   
	/** The range predicate. This will be "true" if !explicitRange. */
    public final Expression range;
    
	/** The body expression. */
	public final Expression body;
    
    /** The scope. */
    private BlockScope scope;
    
    /** A flag indicating whether the range was specified explicitly. */
    private final boolean explicitRange; 
    
    /** A flag indicating whether the bound variables/internal scope have been resolved. */
    private boolean internalsResolved;
    
    /**
     * Constructs a JmlQuantifiedExpression with the specified parameters.
     * 
     * @param lexeme The lexeme of the quantifier as a String.
     * @param range The range predicate. Null, if none was specified explicitly.
     * @param body The body expression.
     * @param sourceStart The source start marker.
     */
	public JmlQuantifiedExpression(String lexeme, 
			/*@nullable*/ Expression range, 
			Expression body, 
			LocalDeclaration[] boundVariables, 
			int sourceStart) {
		quantifier = JmlQuantifier.fromLexeme(lexeme);
		this.explicitRange = range != null;
		this.range = explicitRange ? range : rangeExprWhenNotSpecified(sourceStart);
		this.body = body;
		this.boundVariables = boundVariables;
		this.sourceStart = sourceStart - 1;
		this.sourceEnd = body.sourceEnd() + 1;
		constant = Constant.NotAConstant;
		internalsResolved = false;
	}
	
	/**
	 * Returns a TRUE Expressions AST node that can be used as a range when the range is not
	 * explicitly given.
	 */ 
	public /*@helper*/ Expression rangeExprWhenNotSpecified(int quantSourceStart) {
		// we need the range to be true if it isn't specified, and this is the best
		// we can do for its nonexistent "location" in the code
		return new TrueLiteral(quantSourceStart, quantSourceStart);
	}
	
	/** {@inheritDoc} */
	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		resolveInternals(currentScope);
		FlowInfo preAnalysisFlowInfo = flowInfo.copy();
		
		// code analysis of bound variables
		for (int i = 0; i < boundVariables.length; i++) {
			LocalDeclaration boundVar = boundVariables[i];
			flowInfo = boundVar.analyseCode(scope, flowContext, flowInfo);
			//LocalDeclaration's analysis won't markAsDefinitelyNonNull or markAsPotentiallyNull 
			//because these bound variables don't have an initialization
			if (boundVar.binding != null) {
				flowInfo.markAsDefinitelyAssigned(boundVar.binding);
				if (!Nullity.isPrimitiveType(boundVar.binding.type) && boundVar.type instanceof JmlTypeReference) {
					Nullity nullity = ((JmlTypeReference) boundVar.type).getNullity();
					if (nullity.isNon_null())
						flowInfo.markAsDefinitelyNonNull(boundVar.binding);
					else
						flowInfo.markAsPotentiallyNull(boundVar.binding);
				}				
			}
		}

		// code analysis of range
		FlowInfo rangeInfo = range.analyseCode(scope, flowContext, flowInfo);
					
		// code analysis of body (see IfStatement's analyseCode)
		FlowInfo bodyInfo = rangeInfo.safeInitsWhenTrue();
		if (this.body != null) {
			if (!this.body.complainIfUnreachable(bodyInfo, scope, false)) {
				bodyInfo =	this.body.analyseCode(scope, flowContext, bodyInfo);
			}
		}	
		
		return preAnalysisFlowInfo;
	}

	/** {@inheritDoc} */
	public StringBuffer printExpression(int indent, StringBuffer output) {
		output.append('(').append(quantifier.lexeme).append(' ');
		int dimensions = boundVariables[0].type.dimensions();
		output.append(boundVariables[0].type.getLastToken());
		for (int i = 1; i < boundVariables.length; i++) {
			dimensions = Math.min(dimensions, boundVariables[i].type.dimensions());
		}
		for (int i = 0; i < dimensions; i++) {
			output.append("[]"); //$NON-NLS-1$
		}
		output.append(' ').append(boundVariables[0].name);
		for (int i = dimensions; i < boundVariables[0].type.dimensions(); i++) {
			output.append("[]"); //$NON-NLS-1$
		}
		for (int i = 1; i < boundVariables.length; i++) {
			output.append(", ").append(boundVariables[i].name); //$NON-NLS-1$
			for (int j = dimensions; j < boundVariables[i].type.dimensions(); j++) {
				output.append("[]"); //$NON-NLS-1$
			}
		}
		output.append("; "); //$NON-NLS-1$
		if (explicitRange) {
			range.printExpression(0, output);
			output.append("; "); //$NON-NLS-1$
		}
		body.printExpression(0, output);
		return output.append(')');
	}


	/** {@inheritDoc} */
	public TypeBinding resolveType(BlockScope upperScope) {
		// we must resolve the bound variables in order to determine the type of the quantifier,
		// at least in cases where the type is the body type
		resolveInternals(upperScope);
		
		if (quantifier.type != null) {
			resolvedType = quantifier.type;
		} else if ((body.resolvedType != null) && quantifier.isLegalType(body.resolvedType)) {
			resolvedType = body.resolvedType;
		} else {
			// if the body type is illegal, the error will be caught elsewhere; there's no need
			// to compound it with further error messages by saying that the whole quantifier 
			// is of an illegal type.
			resolvedType = quantifier.getFirstLegalType();
		}
		return resolvedType;
	}
	
	/** {@inheritDoc} */
	public void generateCode(BlockScope currentScope, CodeStream codeStream, boolean valueRequired) {
		quantifier.generateCode(boundVariables, range, body, currentScope, codeStream, valueRequired);
	}
	
	/**
	 * Resolves the internal components of this quantifier (body, range, bound variables), 
	 * creating a new scope for the bound variables. This method has no effect when called
	 * a second (or subsequent) time.
	 * 
	 * @param upperScope The scope in which to resolve the quantifier.
	 */
	private void resolveInternals(BlockScope upperScope) {		
		if (!internalsResolved) {
			// create a scope for the bound variables and populate it
			scope = new BlockScope(upperScope);
			for (int i = 0; i < boundVariables.length; i++) { 
				boundVariables[i].resolve(scope);
			}
		
			// resolve/typecheck the range expression
			range.resolveTypeExpecting(scope, TypeBinding.BOOLEAN);
		
			// resolve/typecheck the body expression
			body.resolveType(scope);
			if ((body.resolvedType != null) && !quantifier.isLegalType(body.resolvedType)) {
				scope.problemReporter().typeMismatchError(body.resolvedType, quantifier.getFirstLegalType(), body, body);
			} 
		
			internalsResolved = true;
		}
	}
	public void traverse(ASTVisitor visitor, BlockScope blockScope) {
		visitor.visit(this, blockScope);
		visitor.endVisit(this,blockScope);
	}
}
