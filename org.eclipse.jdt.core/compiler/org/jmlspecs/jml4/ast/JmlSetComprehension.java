package org.jmlspecs.jml4.ast;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.LocalDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MessageSend;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.FlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.impl.Constant;
import org.eclipse.jdt.internal.compiler.lookup.BlockScope;
import org.eclipse.jdt.internal.compiler.lookup.ParameterizedTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeConstants;

public class JmlSetComprehension extends Expression {
	
	/** Method name constant for "contains". */
	private static final char[]   CONTAINS             = "contains".toCharArray(); //$NON-NLS-1$
	
	/** Method name constant for "has". */
	private static final char[]   HAS                  = "has".toCharArray(); //$NON-NLS-1$
	
	/** Package name constant for "models". */
	private static final char[]   JML_MODELS           = "models".toCharArray(); //$NON-NLS-1$
	
	/** Class name constant for JMLObjectSet. */
	private static final char[][] JML_OBJECT_SET       = {TypeConstants.JML_ORG, TypeConstants.JMLSPECS, JML_MODELS, "JMLObjectSet".toCharArray()}; //$NON-NLS-1$

	/** Class name constant for JMLValueSet. */
	private static final char[][] JML_VALUE_SET        = {TypeConstants.JML_ORG, TypeConstants.JMLSPECS, JML_MODELS, "JMLValueSet".toCharArray()}; //$NON-NLS-1$

	/** Class name constant for Collection. */
	private static final char[][] JAVA_UTIL_COLLECTION = {TypeConstants.JAVA, TypeConstants.UTIL, "Collection".toCharArray()}; //$NON-NLS-1$
	
	/** Class name constant for JMLType. */
	private static final char[][] JML_TYPE             = {TypeConstants.JML_ORG, TypeConstants.JMLSPECS, JML_MODELS, "JMLType".toCharArray()}; //$NON-NLS-1$

	/** 
	 * A map from legal collection types for comprehension to the acceptable method names to be used
	 * to test membership in those types. The keys in this map are char[][] (because we need to resolve
	 * the types at compile time), and the values are char[]. 
	 */
	private static final Map MembershipCallMap = new HashMap();
	
	/**
	 * A set of legal types for the set comprehension as a whole. The values are char[][] (because
	 * we need to resolve the types at compile time). 
	 */
	private static final Set LegalTypes = new HashSet();
	
	/** The type. */
	private TypeReference typeRef;
   
    /** The bound variable (as a local declaration). */
    public final LocalDeclaration boundVariable;
    
	/** The superset predicate. */
    public final Expression supersetPredicate;
    
	/** The main predicate. */
	public final Expression predicate;
    
    /** The scope. */
    private BlockScope scope;
    
    /** A flag indicating whether the bound variables/internal scope have been resolved. */
    private boolean internalsResolved;
    
    /**
     * Constructs a JmlSetComprehension with the specified parameters. Note that the type still
     * needs to be specified separately, before any code analysis or type resolution is done; 
     * similarly, the source start needs to be specified later. 
     * 
     * @param boundVariable The bound variable.
     * @param supersetPredicate The superset predicate.
     * @param predicate The main predicate.
     */
	public JmlSetComprehension(LocalDeclaration boundVariable, 
			Expression supersetPredicate,
			Expression predicate) {
		this.boundVariable = boundVariable;
		this.supersetPredicate = supersetPredicate;
		this.predicate = predicate;
		this.sourceEnd = predicate.sourceEnd() + 1;
		constant = Constant.NotAConstant;
		internalsResolved = false;
	}
	
	/**
	 * Sets the type (using a type reference).
	 * 
	 * @param typeRef The type reference.
	 */
	public void setTypeReference(TypeReference typeRef) {
		this.typeRef = typeRef;
	}
	
	/** {@inheritDoc} */
	public FlowInfo analyseCode(BlockScope currentScope, FlowContext flowContext, FlowInfo flowInfo) {
		resolveInternals(currentScope);
		
		// code analysis of bound variables
		flowInfo = boundVariable.analyseCode(scope, flowContext, flowInfo);
		if (boundVariable.binding != null) {
			flowInfo.markAsDefinitelyAssigned(boundVariable.binding);
		}
		
		// code analysis of superset predicate
		flowInfo = supersetPredicate.analyseCode(scope, flowContext, flowInfo);
		
		// code analysis of main predicate
		flowInfo = predicate.analyseCode(scope, flowContext, flowInfo);
		
		return flowInfo;
	}

	/** {@inheritDoc} */
	public StringBuffer printExpression(int indent, StringBuffer output) {
		output.append("new "); //$NON-NLS-1$
		typeRef.printExpression(0, output);
		output.append(" {"); //$NON-NLS-1$
		boundVariable.type.printExpression(0, output);
		output.append(' ').append(boundVariable.name).append(" | "); //$NON-NLS-1$
		supersetPredicate.printExpression(0, output);
		output.append(" && "); //$NON-NLS-1$
		predicate.printExpression(0, output);
		output.append('}');
		return output;
	}

	/** {@inheritDoc} */
	public TypeBinding resolveType(BlockScope upperScope) {
		// we must resolve the bound variables in order to determine whether 
		// the specified type of the set comprehension is valid
		resolveInternals(upperScope);
		return typeRef.resolvedType;
	}
	
	/** {@inheritDoc} */
	public void generateCode(BlockScope currentScope, CodeStream codeStream, boolean valueRequired) {
		if (!valueRequired) {
			return;
		}
		
		// for now, this method just creates an empty set of the appropriate type so code with RAC still works. 
		
		// our resolved type must in fact be a ReferenceBinding; if not, we have serious issues, 
		// but we'll check anyway
		if (typeRef.resolvedType instanceof ReferenceBinding) {
			ReferenceBinding refBinding = (ReferenceBinding) typeRef.resolvedType;
			int pc = codeStream.position;
			codeStream.new_(refBinding);
			if (valueRequired) {
				codeStream.dup();
			}
			codeStream.recordPositionsFrom(pc, typeRef.sourceStart);
			codeStream.invokespecial(refBinding.getExactConstructor(new TypeBinding[] {}));
			codeStream.recordPositionsFrom(pc, sourceStart);
			// at this point, we would fill this new set with the values, obtained by iterating over
			// the message receiver of the superset predicate, for which the main predicate evaluates to true;
			// this is essentially inlining a while loop and an if-then statement
		} 
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
			// create a scope for the bound variable and populate it
			scope = new BlockScope(upperScope);
			boundVariable.resolve(scope);
		
			// resolve the set comprehension type reference; it must be a valid type
			Iterator iterator = LegalTypes.iterator();
			boolean typeOK = false;
			
			typeRef.resolve(upperScope);
			while (!typeOK && iterator.hasNext()) {
				char[][] compoundName = (char[][]) iterator.next();
				TypeBinding type = scope.getType(compoundName, compoundName.length);
				// we compare the type erasures to future-proof for when we implement parameterized
				// versions of JMLObjectSet and JMLValueSet
				if (typeRef.resolvedType.erasure().isEquivalentTo(type.erasure())) {
					typeOK = true;
					// if typeRef is JMLValueSet, then the bound variable must be compatible with JMLType
					if (compoundName == JML_VALUE_SET) {
						TypeBinding jmlType = scope.getType(JML_TYPE, JML_TYPE.length);
						if (!boundVariable.type.resolvedType.isCompatibleWith(jmlType)) {
							scope.problemReporter().typeMismatchError(boundVariable.type.resolvedType, jmlType, typeRef, typeRef);
						}
					}
					// if typeRef is parameterized, then the bound variable must be compatible with the parameter
					if (typeRef.resolvedType.isParameterizedType()) {
						ParameterizedTypeBinding ptBinding = (ParameterizedTypeBinding) typeRef.resolvedType;
						// we assume there's one parameter
						if (!boundVariable.type.resolvedType.isCompatibleWith(ptBinding.arguments[0])) {
							scope.problemReporter().typeMismatchError(boundVariable.type.resolvedType, ptBinding.arguments[0], typeRef, typeRef);
						}
					}
				}
			}
			
			if (!typeOK) {
				scope.problemReporter().illegalTypeForSetComprehension(typeRef);
			}
			
			// resolve/typecheck the superset predicate; not only does it have to be boolean, but 
			// it also has to actually be a method call to one of the valid methods, on an object of
			// one of the valid types that, if it is generic, contains elements that can be assigned
			// to the bound variable's type (if it is not generic we can't do that check). 
			supersetPredicate.resolveTypeExpecting(scope, TypeBinding.BOOLEAN);
			boolean callOK = false; 
			
			if (supersetPredicate instanceof MessageSend) {
				MessageSend supersetCall = (MessageSend) supersetPredicate;
				iterator = MembershipCallMap.keySet().iterator();
				
				while (!callOK && iterator.hasNext()) {
					char[][] compoundName = (char[][]) iterator.next();
					TypeBinding type = scope.getType(compoundName, compoundName.length);
					
					// we compare the type erasures, because the generic parameter will be checked later
					if (supersetCall.actualReceiverType.erasure().isCompatibleWith(type.erasure()) &&
							Arrays.equals(supersetCall.selector, (char[]) MembershipCallMap.get(compoundName)) &&
							supersetCall.arguments.length == 1 && 
							supersetCall.arguments[0].localVariableBinding() == boundVariable.binding) {
						callOK = true;
						
						// is the element type of the set/collection, if specified, compatible with the type
						// of the bound variable? if the bound variable is not a supertype of the set/collection
						// element type, or if the set/collection is unparameterized and the bound variable is not
						// Object (or JMLType for JMLValueSet), we get a warning
						boolean conversionOK = true;
						TypeBinding elementType = scope.getJavaLangObject();
				
						if (supersetCall.actualReceiverType.isParameterizedType()) {
							ParameterizedTypeBinding ptBinding = (ParameterizedTypeBinding) supersetCall.actualReceiverType;
							elementType = ptBinding.arguments[0];
							conversionOK = (ptBinding.arguments.length == 1) &&
								ptBinding.arguments[0].isCompatibleWith(boundVariable.type.resolvedType);
						} else if (supersetCall.actualReceiverType.erasure().isEquivalentTo(scope.getType(JML_VALUE_SET, JML_VALUE_SET.length))) {
							elementType = scope.getType(JML_TYPE, JML_TYPE.length);
							conversionOK = elementType.isCompatibleWith(boundVariable.type.resolvedType);
						} else if (!scope.getJavaLangObject().isEquivalentTo(boundVariable.type.resolvedType)) {
							conversionOK = false;
						}
						
						if (!conversionOK) {
							scope.problemReporter().unsafeTypeConversion(supersetPredicate, elementType, boundVariable.type.resolvedType);
						}
					}
				}
			} 

			if (!callOK) {
				// anything other than a valid set membership method call causes an error
				scope.problemReporter().illegalExpressionForSetMembership(supersetPredicate, boundVariable);
			}
			 
			// resolve/typecheck the main predicate; it must also be Boolean
			predicate.resolveTypeExpecting(scope, TypeBinding.BOOLEAN);
		
			internalsResolved = true;
		}
	}
	
	// Static initializer, creates the map of acceptable methods for set membership testing and the map
	// of acceptable set comprehension types.
	
	static {
		MembershipCallMap.put(JAVA_UTIL_COLLECTION, CONTAINS); 
		MembershipCallMap.put(JML_OBJECT_SET, HAS); 
		MembershipCallMap.put(JML_VALUE_SET, HAS); 
		
		LegalTypes.add(JML_OBJECT_SET);
		LegalTypes.add(JML_VALUE_SET);
	}
}
