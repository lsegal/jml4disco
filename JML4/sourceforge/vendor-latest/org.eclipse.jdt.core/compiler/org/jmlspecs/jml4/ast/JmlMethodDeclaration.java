package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ClassFile;
import org.eclipse.jdt.internal.compiler.CompilationResult;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.codegen.CodeStream;
import org.eclipse.jdt.internal.compiler.flow.ExceptionHandlingFlowContext;
import org.eclipse.jdt.internal.compiler.flow.FlowInfo;
import org.eclipse.jdt.internal.compiler.flow.InitializationFlowContext;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.compiler.JmlConstants;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlMethodDeclaration extends MethodDeclaration implements JmlAbstractMethodDeclaration {
	
	public static final boolean DEBUG = false;
	public static final boolean DEBUG_NULLITY_OF_OVERRIDES = false;
	public JmlMethodSpecification specification;
	public JmlLocalDeclaration resultValue;
	private boolean jmlModifiersHaveBeenInit = false;
	private long jmlModifiers = 0;
	// escResults only set after esc4 is run on this method.
	private /*@nullable*/Result[] escResults;
	private boolean previousRacState;

	public JmlMethodDeclaration(CompilationResult compilationResult) {
		super(compilationResult);
	}
	public void resolve(ClassScope upperScope) {
		initJmlModifiersFromAnnotations();
		super.resolve(upperScope);
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.RESOLVE)
			return;

		if (this.specification == null)
			return;
		if (this.returnType != null && this.returnType.resolvedType != TypeBinding.VOID) {
			this.createLocalForResult();
			this.resultValue.resolve(this.scope);
			this.scope.addLocalVariable(this.resultValue.binding);
			this.resultValue.binding.recordInitializationStartPC(0);
		}
		this.specification.resolve(this.scope);
	}

	public void initJmlModifiersFromAnnotations() {
		jmlModifiers |= JmlModifier.getFromAnnotations(this.annotations);
		this.jmlModifiersHaveBeenInit = true;
	}

	public void resolveStatements() {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.RESOLVE
			&& this.isModel())
			return;
		super.resolveStatements();
	}

	public void analyseCode(ClassScope classScope, InitializationFlowContext initializationContext, FlowInfo flowInfo) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_ANALYSIS) {
			if (!this.isModel())
				super.analyseCode(classScope, initializationContext, flowInfo);
			return;
		}

		// TODO uncomment the following line
		// checkNullityOfSupers(classScope);
		// TODO: remove the following test once we fix the parser to only use
		// Jml AST Nodes when EnabledJml.
		if (DEBUG_NULLITY_OF_OVERRIDES) {
			MethodBinding[] overridden = this.binding.overriddenInheritedMethods;
			System.out.println(new String(this.binding.declaringClass.sourceName)+"."+new String(this.binding.selector)); //$NON-NLS-1$
			outputOverriddenMethods(overridden, 1);
		}

		ExceptionHandlingFlowContext methodContext =
			new ExceptionHandlingFlowContext(
				initializationContext,
				this,
				this.binding.thrownExceptions,
				this.scope,
				FlowInfo.DEAD_END);

		if (classScope.compilerOptions().useNonNullTypeSystem()) {
			tagParametersWithNullities(this, flowInfo);
		}
		// It would be better if we could call analyseCode on 
		//  1) the method's parameters, 
		//  2) the requires clause, 
		//  3) the ensures clause, then 
		//  4) super.
		// Statements' analyseCode returns a flowInfo, but the ones in (Abstract)MethodDeclaration do not.
		if (classScope.compilerOptions().jmlDbcEnabled && this.specification != null) {
			if (this.resultValue != null) {
				flowInfo.markAsDefinitelyAssigned(this.resultValue.binding);
				this.resultValue.binding.useFlag = LocalVariableBinding.USED;
			}
			// tag parameters as being set
			if (this.arguments != null) {
				for (int i = 0, count = this.arguments.length; i < count; i++) {
					flowInfo.markAsDefinitelyAssigned(this.arguments[i].binding);
				}
			}
			this.specification.analysePrecondition(this.scope, methodContext, flowInfo);
			this.specification.analysePostcondition(this.scope, methodContext, flowInfo);
		}
		handleArgumentsAnnotations(this.arguments, classScope);
		//Set nullity for method's return type through its annotations
		if (classScope.compilerOptions().useNonNullTypeSystem()) {
			if (this.annotations != null) {
				returnType.handleAnnotations(this.annotations, classScope.problemReporter()); 
			}
		}
		super.analyseCode(classScope, initializationContext, flowInfo);
		
		if (classScope.compilerOptions().useNonNullTypeSystem() && !this.isStatic())
			checkNullityOfOverriddenMethods(classScope);
		if (isPure())
			checkPurity();
		
	}

	/*package*/ static void handleArgumentsAnnotations(Argument[] arguments, ClassScope scope) {
		if (! scope.compilerOptions().useNonNullTypeSystem())
			return;
		//Set nullity for method parameters through their annotations
		ProblemReporter problemReporter = scope.problemReporter();
		int length = arguments == null ? 0 : arguments.length;
		for (int i = 0; i < length; i++) {
			Argument argument = arguments[i];
			if (argument.annotations != null) {
				argument.type.handleAnnotations(argument.annotations, problemReporter);
			}
		}
	}

	private void checkPurity() {
		// TODO: implement purity check
	}

	private void checkNullityOfOverriddenMethods(ClassScope classScope) {
		if (this.binding.overriddenInheritedMethods == null)
			return;
		
		for (int i = 0; i < this.binding.overriddenInheritedMethods.length; i++) {
			if (this.binding.overriddenInheritedMethods[i] == null)
				continue;
			AbstractMethodDeclaration decl = this.binding.overriddenInheritedMethods[i].sourceMethod();
			if (decl == null)
				continue;
			if (decl.binding == null)
				decl.binding = this.binding.overriddenInheritedMethods[i];
			if (DEBUG_NULLITY_OF_OVERRIDES)
				System.out.println(""+ new String(this.binding.declaringClass.sourceName) +"."+ new String(this.selector) + " - "+new String(decl.binding.declaringClass.sourceName)); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			if (!this.isConstructor() && !decl.isConstructor())
				checkNullityOfOverriddenMethodsReturnType(classScope, (MethodDeclaration)decl);
			checkNullityOfOverriddenMethodsParameters(classScope, decl);
		}
	}

	private void checkNullityOfOverriddenMethodsReturnType(ClassScope classScope, MethodDeclaration decl) {
		if (DEBUG_NULLITY_OF_OVERRIDES)
			System.out.println("\t return type is "+ this.returnType.toString() +" vs "+ decl.returnType.toString()); //$NON-NLS-1$ //$NON-NLS-2$
		if (nullityIncompatible(this.returnType, decl.returnType, true)) {
			if (DEBUG_NULLITY_OF_OVERRIDES)
				System.out.println("\t complaining"); //$NON-NLS-1$ 
			classScope.problemReporter().incompatibleReturnTypeNullity(this, decl.binding.declaringClass);
		}
		else
			if (DEBUG_NULLITY_OF_OVERRIDES)
				System.out.println("\t not complaining"); //$NON-NLS-1$
	}

	private void checkNullityOfOverriddenMethodsParameters(ClassScope classScope, AbstractMethodDeclaration decl) {
		if (this.arguments == null)
			return;
		int length = Math.min(this.arguments.length, decl.arguments.length);
		for (int i=0; i<length; i++) {
			checkNullityOfOverriddenMethodsParameter(classScope, this.arguments[i], decl.arguments[i], decl.binding.declaringClass);
		}
	}

	private void checkNullityOfOverriddenMethodsParameter(ClassScope classScope, Argument currentsArg, Argument inheritedsArg, ReferenceBinding inheritedFrom) {
		if (nullityIncompatible(currentsArg.type, inheritedsArg.type, false)) {
			classScope.problemReporter().incompatibleParameterNullity(currentsArg, inheritedFrom);
		}
	}
	private boolean nullityIncompatible(TypeReference actual, TypeReference overridden, boolean isCheckingReturnNullity) {
		if (actual.resolvedType == null || actual.resolvedType.isBaseType()) {
			return false;
		}
		if (actual instanceof JmlTypeReference && overridden instanceof JmlTypeReference) {
			JmlTypeReference actualTypeRef = (JmlTypeReference) actual;
			JmlTypeReference overriddenTypeRef = (JmlTypeReference) overridden;
            Nullity actualNullity = actualTypeRef.getNullity();
            Nullity overriddenNullity = overriddenTypeRef.getNullity();
            if (isCheckingReturnNullity)
                return (actualNullity.isNullable() && overriddenNullity.isNon_null());
            else
                return (actualNullity.isNullable() != overriddenNullity.isNullable());
		}
		return false;
	}

	//@ requires this.returnType != null && this.returnType.resolvedType != TypeBinding.VOID;
	//@ ensures  this.resultValue != null && this.resultValue.binding != null;
	private void createLocalForResult() {
		JmlLocalDeclaration result = new JmlLocalDeclaration("Jml$result".toCharArray(), 0, 0); //$NON-NLS-1$
		result.type = this.returnType;
		final TypeBinding resolvedType = (result.type == null) ? null : result.type.resolvedType;
		result.binding = new LocalVariableBinding(result, resolvedType, 0, false);
		result.bits |= ASTNode.IsLocalDeclarationReachable | ASTNode.FirstAssignmentToLocal ; // only set if actually reached
		this.resultValue = result; 
	} 


	private void outputOverriddenMethods(MethodBinding[] overridden, int indent) {
		StringBuffer temp = new StringBuffer(indent);
		for (int i=0; i<indent; i++) {
			temp.append('\t');
		}
		String tabs = temp.toString();
		if (overridden == null) {
			System.out.println(tabs+" overridden == null"); //$NON-NLS-1$
		} else {
			for (int i = 0; i < overridden.length; i++) {
				System.out.println(tabs+" overrides "+new String(overridden[i].selector)+" in "+new String(overridden[i].declaringClass.sourceName)); //$NON-NLS-1$ //$NON-NLS-2$
				outputOverriddenMethods(overridden[i].overriddenInheritedMethods, indent+1);
			}
		}
	}

	/* package */ static void tagParametersWithNullities(AbstractMethodDeclaration _this,
			FlowInfo flowInfo) {
		if (_this.arguments == null)
			return;

		for (int i = 0, count = _this.arguments.length; i < count; i++) {
			Argument argument = _this.arguments[i];
			// just to grow, flags will be overwritten just below
			flowInfo.markAsDefinitelyAssigned(argument.binding);
			if (!Nullity.isPrimitiveType(argument.binding.type)
					&& argument.type instanceof JmlTypeReference) {
				Nullity nullity = ((JmlTypeReference) argument.type)
						.getNullity();
				if (nullity.isNon_null())
					flowInfo.markAsDefinitelyNonNull(argument.binding);
				else
					flowInfo.markAsPotentiallyNull(argument.binding);
			}
		}
	}
	
/*	private void checkNullityOfSupers(ClassScope classScope) {
		AbstractMethodDeclaration[] supers = MethodOverrideFinder.findOverriddenMethods(this, classScope);
		for (int i = 0; i < supers.length; i++) {
			if (supers[i] instanceof MethodDeclaration) {
				MethodDeclaration zuper = (MethodDeclaration)supers[i];
				checkReturnType(this.returnType, zuper.returnType, classScope);
                // TODO: uncomment the following line & implement checkParameters.
				//checkParameters(...);
			}
		}
	}
*/	
/*	private void checkReturnType(TypeReference thisReturn, TypeReference superReturn, Scope scope) {
		Nullity  thisNullity = ( thisReturn instanceof JmlTypeReference ? ((JmlTypeReference) thisReturn).getNullity() : null);
		Nullity superNullity = (superReturn instanceof JmlTypeReference ? ((JmlTypeReference)superReturn).getNullity() : null);
		if (thisNullity == Nullity.nullable && superNullity == Nullity.non_null) {
				scope.problemReporter().attemptBroadenReturnNullity(this, superReturn);
		}
	}
*/

	public void generateCode(ClassFile classFile) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_GENERATION
			&& this.isModel()) // if this is not a model method we still want to generate code for the method body.
			return;
		super.generateCode(classFile);
		if (this.scope.compilerOptions().jmlEscGovernsRac) {
			this.scope.compilerOptions().jmlRacEnabled = this.previousRacState;
		}
	}

	protected void generateChecksForPrecondition(MethodScope currentScope, CodeStream codeStream) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_GENERATION)
			return;
		JmlMethodDeclaration.generateChecksForNonNullParametersStatic(this, codeStream);
		if (this.specification != null) {
			if (this.resultValue != null)
				codeStream.addVariable(this.resultValue.binding);
			this.specification.generateCheckOfRequires(currentScope, this, codeStream);
		}
		if (currentScope.compilerOptions().jmlEscGovernsRac) {
			this.previousRacState = currentScope.compilerOptions().jmlRacEnabled;
			if (escSayNoNeedToCheck(this.escResults)) {
				currentScope.compilerOptions().jmlRacEnabled = false;
			}
		}
	}

	protected void generateChecksForPostcondition(MethodScope mScope, CodeStream codeStream) {
		if (JmlConstants.LAST_PROCESSING_STAGE < JmlConstants.CODE_GENERATION)
			return;
		if (this.specification != null) {
			this.specification.generateCheckOfEnsures(mScope, this, codeStream);
		}
	}
	
	/*package*/ static boolean escSayNoNeedToCheck(/*@nullable*/Result[] escResults) {
		if (escResults == null)
			return false;
		return Result.isValid(escResults);
	}

	/* package */ static void generateChecksForNonNullParametersStatic(AbstractMethodDeclaration methodDecl, CodeStream codeStream) {
		if (!methodDecl.scope.compilerOptions().jmlRacEnabled || methodDecl.arguments == null)
			return;
	
		for (int i = 0, count = methodDecl.arguments.length; i < count; i++) {
			Argument argument = methodDecl.arguments[i];
			if (argument.type instanceof JmlTypeReference) {
				Nullity nullity = ((JmlTypeReference) argument.type).getNullity();
				LocalVariableBinding localBinding = argument.binding;
				if (localBinding != null
						&& !Nullity.isPrimitiveType(localBinding.type)
						&& nullity != null && nullity.isNon_null()) {
					generateTestForNonNull(codeStream, localBinding);
				}
			}
		}
	}

	private static void generateTestForNonNull(CodeStream codeStream, LocalVariableBinding localBinding) {
		codeStream.load(localBinding);
		JmlCastExpression .generateNullityTest(
						codeStream,
						"java/lang/NullPointerException",  //$NON-NLS-1$
						"RAC: parameter " + new String(localBinding.name) + " is null but was declared to be non-null"); //$NON-NLS-1$ //$NON-NLS-2$ 
		codeStream.pop();
	}
	
	public boolean isPure() {
		if (!this.jmlModifiersHaveBeenInit)
			initJmlModifiersFromAnnotations();
		return JmlModifier.isPure(this.jmlModifiers);
	}

	public boolean isModel() {
		if (!this.jmlModifiersHaveBeenInit)
			initJmlModifiersFromAnnotations();
		return JmlModifier.isModel(this.jmlModifiers);
	}

	public void setEscResults(Result[] results) {
		this.escResults = results;
	}
	
	public void traverse(ASTVisitor visitor,ClassScope classScope) {
		if (visitor.visit(this, classScope)) {
			if (this.specification != null) {
				this.specification.traverse(visitor, this.scope);
			}
			super.traverse(visitor, classScope);
		}
		visitor.endVisit(this, classScope);
	}

	public JmlMethodSpecification getSpecification() {
		return this.specification;
	}
}