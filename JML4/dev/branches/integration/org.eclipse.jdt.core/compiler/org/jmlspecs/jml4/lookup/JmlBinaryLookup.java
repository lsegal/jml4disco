package org.jmlspecs.jml4.lookup;

import java.io.File;

import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.env.IBinaryType;
import org.eclipse.jdt.internal.compiler.env.ICompilationUnit;
import org.eclipse.jdt.internal.compiler.env.NameEnvironmentAnswer;
import org.eclipse.jdt.internal.compiler.lookup.BaseTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.BinaryTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.ast.JmlAstUtils;
import org.jmlspecs.jml4.ast.JmlTypeReference;
import org.jmlspecs.jml4.compiler.JmlConstants;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlBinaryLookup {
	private static final boolean DEBUG = false;
	private final JmlSourceLookup jmlSourceLookup;

	public JmlBinaryLookup(JmlSourceLookup jmlSourceLookup) {
		this.jmlSourceLookup = jmlSourceLookup;
	}
	
	/**
	 *   1. find source/spec file {.java, .jml, .refines-spec, etc.} for a given .class file.
	 *   2. perform a diet parse on the file(s) found to get signature.
	 *   3. store the source/spec type declaration(s) in the binding.
	 *   
	 * @param binaryType the class to modify
	 * @param binding 
	 */
	 // [PC] The following is the previous implementation of decorateBindingWithJml
	 // I am keeping it here until I have fully replaced it.
	public void decorateBindingWithJml(IBinaryType binaryType, BinaryTypeBinding binding) {
		// these 3 lines are to stop the infinite looping...
		if (binding.jmlBinaryLookupDecorateBindingWithJmlCalled) 
			return;
		binding.jmlBinaryLookupDecorateBindingWithJmlCalled = true;
		
		String binaryName = new String(binaryType.getName());
        File[] files = this.jmlSourceLookup.getJmlFileFinder().find(binaryName);
        if (DEBUG) System.out.println("JmlBinaryLookup: found " + files.length + " file(s) for  '" + new String(binaryType.getName()) + JmlConstants.SQUOTE); //$NON-NLS-1$ //$NON-NLS-2$
        CompilationUnitDeclaration[] units = this.jmlSourceLookup.parse(files);
        for (int i = 0; i < units.length; i++) {
        	CompilationUnitDeclaration unitDecl = units[i];
			if (unitDecl.types != null) {
				for (int j = 0; j < unitDecl.types.length; j++) {
					TypeDeclaration type = unitDecl.types[j];
		    		if (binding.typeDeclaration == null)
			    		binding.typeDeclaration = type;
		    		else {
		    			ProblemReporter pr = unitDecl.problemReporter;
						this.jmlSourceLookup.merge(pr, binding.typeDeclaration, type);
		    		}
				}
        	}
		}
	}
	
	public void decorateBindingWithJml_new(IBinaryType binaryType, BinaryTypeBinding binding) {
		// these 3 lines are to stop the infinite looping...
		if (binding.jmlBinaryLookupDecorateBindingWithJmlCalled) 
			return;
		binding.jmlBinaryLookupDecorateBindingWithJmlCalled = true;
		
		NameEnvironmentAnswer answer = this.jmlSourceLookup.getJmlFileFinder().sourceNameEnv.findType(binding.compoundName);
		if (answer == null)
			return; // no source found
		ICompilationUnit cu = answer.getCompilationUnit();
        CompilationUnitDeclaration unitDecl = this.jmlSourceLookup.dietParse(cu);
        char [][] name = new char[][] { binding.compoundName[binding.compoundName.length-1] };
        TypeDeclaration typeDecl = unitDecl.declarationOfType(name);
        // The given typeDecl has no associated binding ... it might be best to always merge.
        if (binding.typeDeclaration == null)
        	binding.typeDeclaration = typeDecl;
        else
        	this.jmlSourceLookup.merge(unitDecl.problemReporter, binding.typeDeclaration, typeDecl);
	}
	
//	private void mergeSpecIntoBinding(/*@non_null*/ IBinaryType binaryType, /*@non_null*/ ReferenceBinding binding, TypeDeclaration typeDeclaration) {
//		if (typeDeclaration.fields != null && typeDeclaration.fields.length > 0)
//			mergeFields(binding.fields(), typeDeclaration.fields);
//		if (typeDeclaration.methods != null && typeDeclaration.methods.length > 0)
//			mergeMethods(binding.methods(), typeDeclaration.methods);
//	}
	private void mergeWithSource(ProblemReporter problemReporter, ReferenceBinding referenceBinding) {
		String unitName = new String(referenceBinding.constantPoolName());
		String sourceFileName = new String(referenceBinding.getFileName());
		File sourceFile = new File(sourceFileName);
		File[] files = sourceFile.exists()
						? new File[] { sourceFile }
        				: this.jmlSourceLookup.getJmlFileFinder().findSource(unitName);
		if (files.length == 0) {
			files = this.jmlSourceLookup.getJmlFileFinder().findSource(sourceFileName.substring(0, sourceFileName.length()-".java".length())); //$NON-NLS-1$
		}
        merge(problemReporter, referenceBinding, unitName, files);
	}
	private void mergeWithSpec(ProblemReporter problemReporter, ReferenceBinding referenceBinding) {
		String unitName = new String(referenceBinding.constantPoolName());
        File[] files = this.jmlSourceLookup.getJmlFileFinder().findSpecs(unitName);
        merge(problemReporter, referenceBinding, unitName, files);
	}
    private void merge(ProblemReporter problemReporter, ReferenceBinding referenceBinding, String unitName, File[] files) {
        if (DEBUG) System.out.println("JmlBinaryLookup: found " + files.length + " file(s) for  '" + unitName + JmlConstants.SQUOTE); //$NON-NLS-1$ //$NON-NLS-2$
        CompilationUnitDeclaration[] specs = this.jmlSourceLookup.parse(files);
		String sourceName = new String(referenceBinding.sourceName());
        for (int i = 0; i < specs.length; i++) {
        	if (specs[i].types != null) {
				for (int j = 0; j < specs[i].types.length; j++) {
					TypeDeclaration spec = specs[i].types[j];
					String specName = new String(spec.name);
					if (sourceName.equals(specName))
						doMerge(problemReporter, referenceBinding, spec);
				}
        	}
		}
	}
	private void doMerge(ProblemReporter problemReporter, ReferenceBinding referenceBinding, TypeDeclaration spec) {
		mergeFields(referenceBinding.fields(), spec.fields);
		mergeMethods(problemReporter, referenceBinding.methods(), spec.methods);
		// TODO: merge member types ?
	}

	public static void mergeMethods(ProblemReporter problemReporter, MethodBinding[] sourceMethods, AbstractMethodDeclaration[] specMethods) {
		if (specMethods == null)
			return;
		for (int i = 0; i < sourceMethods.length; i++) {
			MethodBinding sourceMethod = sourceMethods[i]; 
			AbstractMethodDeclaration specMethod;
			if (i < specMethods.length && signaturesMatch(sourceMethod, specMethods[i])) 
				specMethod = specMethods[i];
			else
				specMethod = findMatchingMethod(sourceMethod, specMethods);
		    if (specMethod != null)
		    	mergeMethod(problemReporter, sourceMethod, specMethod);
		}
	}

	private static /*@ nullable */ AbstractMethodDeclaration findMatchingMethod(MethodBinding sourceMethod, AbstractMethodDeclaration[] specMethods) {
		for (int i = 0; i < specMethods.length; i++) {
			if (signaturesMatch(sourceMethod, specMethods[i]))
				return specMethods[i];
		}
		return null;
	}
	private static /*@ nullable */ FieldDeclaration findMatchingField(FieldBinding sourceField, FieldDeclaration[] specFields) {
		for (int i = 0; i < specFields.length; i++) {
			if (namesMatch(sourceField, specFields[i]))
				return specFields[i];
		}
		return null;
	}

	private static boolean namesMatch(FieldBinding binding, FieldDeclaration declaration) {
		return CharOperation.equals(binding.name, declaration.name);
	}

	public static void mergeFields(FieldBinding[] sourceFields, FieldDeclaration[] specFields) {
		for (int i = 0; sourceFields != null && i < sourceFields.length; i++) {
			FieldBinding sourceField = sourceFields[i];
			if (sourceField == null || sourceField.name == null) continue;
			String sourceFieldName = new String(sourceField.name);
		    FieldDeclaration specField;
		    if (specFields != null && i < specFields.length && specFields[i] != null
		     && specFields[i].name != null && sourceFieldName.equals(new String(specFields[i].name)))
		    	specField = specFields[i];
		    else
		    	specField = JmlSourceLookup.findField(specFields, sourceFieldName);
		    if (specField == null)
		    	continue;
		    
            if (Nullity.isPrimitiveType(sourceField.type))
            	continue;
            
            if (sourceField.fieldDeclaration == null) {
                sourceField.fieldDeclaration = specField;
            } else {
	            Nullity sourceNullity = (sourceField.type instanceof JmlTypeReference ? ((JmlTypeReference) sourceField.type).getNullity() : null);
	            Nullity specNullity   = (specField.type   instanceof JmlTypeReference ? ((JmlTypeReference) specField.type)  .getNullity() : null);
			
	            if (sourceNullity != null && specNullity != null && (sourceNullity.hasExplicitNullity() && specNullity.hasExplicitNullity() && sourceNullity != specNullity)) {
	               System.out.println("issue warning: nullities don't match for field '"+(new String(specField.name))+"' : source("+specField.toString()+") vs spec("+specField.toString()+")"); //TODO: report this problem //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	            }
	            if (sourceField.fieldDeclaration.type != null) {
		            int sourceStart = sourceField.fieldDeclaration.type.sourceStart;
		            int sourceEnd   = sourceField.fieldDeclaration.type.sourceEnd;
		            sourceField.fieldDeclaration.type = specField.type;
		            sourceField.fieldDeclaration.type.sourceStart = sourceStart;
		            sourceField.fieldDeclaration.type.sourceEnd   = sourceEnd;
	            }
            }
		}
	}		
	private static void mergeMethod(ProblemReporter problemReporter, MethodBinding sourceMethod, AbstractMethodDeclaration specMethod) {
		if (sourceMethod.methodDeclaration == null) {
			sourceMethod.methodDeclaration = specMethod;
    		return;
		}
		
		if (sourceMethod.methodDeclaration instanceof MethodDeclaration && specMethod instanceof MethodDeclaration)
			JmlSourceLookup.mergeMethodReturnType(problemReporter, (MethodDeclaration) sourceMethod.methodDeclaration, (MethodDeclaration) specMethod);

		
		Argument[] sourceArguments = sourceMethod.methodDeclaration.arguments;
		if (sourceArguments != null)
			for (int i = 0; i < sourceArguments.length; i++) 
				JmlSourceLookup.mergeMethodParameter(sourceArguments[i], specMethod.arguments[i]);
	}
	private static boolean signaturesMatch(MethodBinding sourceMethodBinding, AbstractMethodDeclaration specMethod) {
		// If the declaration has the binding as its own, then they must match
		if (specMethod.binding != null && specMethod.binding == sourceMethodBinding)
			return true;
		// But there may be other bindings for this method!

		// Method names must match
		if(sourceMethodBinding.selector.length != specMethod.selector.length)
			return false;
		if(! new String(sourceMethodBinding.selector).equals(new String(specMethod.selector)))
			return false;

		// Method return types must match
		if (!returnTypesMatch(sourceMethodBinding, specMethod))
			return false;
		
		// Modifiers must match
		// TODO: add code here.
		
		// Method parameters must match
		TypeBinding[] sourceParams = sourceMethodBinding.parameters;
		Argument[] specArgs= specMethod.arguments;
		
		int sourceLength = sourceParams == null ? 0 : sourceParams.length; 
		int specLength   = specArgs   == null ? 0 : specArgs.length; 
		if (sourceLength != specLength)
			return false;
		for (int i = 0; i < sourceLength; i++) {
			// calculate the equivalent to the constantPoolName for each argument's type name.
			// usually the package information will NOT be available
			TypeBinding  sourceType = sourceParams[i];
			TypeReference specType = specArgs[i].type;
			
            if (! typesMatch(sourceType, specType))
    				return false;
		}
		return true;
	}
	private static boolean returnTypesMatch(MethodBinding binding, AbstractMethodDeclaration abstDecl) {
		final boolean bindingIsConstructor = binding.isConstructor();
		final boolean declIsConstructor = abstDecl.isConstructor();
		if (bindingIsConstructor && declIsConstructor)
			return true;
		if (bindingIsConstructor != declIsConstructor)
			return false;
		if (! (abstDecl instanceof MethodDeclaration))
			return false;

		MethodDeclaration decl = (MethodDeclaration) abstDecl;
				
		return typesMatch(binding.returnType, decl.returnType);
	}

	private static boolean typesMatch(TypeBinding typeBinding, TypeReference typeReference) {
		if (typeBinding == null || typeReference == null)
			return false;
		if (typeBinding.dimensions() != typeReference.dimensions())
			return false;

		String refereceString = JmlAstUtils.concatWith(typeReference.getTypeName(), JmlConstants.SLASH);
		if (typeBinding.isBaseType()) {
			String bindingString = new String(((BaseTypeBinding)typeBinding).simpleName);
			return bindingString.equals(refereceString);
		} else {
			// TODO: can we replace this approximate matching with calls to scope.getTyp(char[])
			//       and make use of the resulting binding in the comparison?
			String bindingString = new String(typeBinding.constantPoolName());
			return (bindingString.indexOf(refereceString) >= 0);
		}
	}

	public void mergeWithSourceAndSpec(ProblemReporter problemReporter, ReferenceBinding referenceBinding) {
		mergeWithSource(problemReporter, referenceBinding);
		mergeWithSpec(problemReporter, referenceBinding);
	}

	public static AbstractMethodDeclaration getDeclaration(MethodBinding binding, BinaryTypeBinding binaryTypeBinding) {
		TypeDeclaration type;
		type = binaryTypeBinding.typeDeclaration;
		if (type == null) {
			// if ((new String(binding.declaringClass.qualifiedSourceName())+"."+new String(binding.constantPoolName())).equals("System.getProperty"))
			// System.out.println("JmlBinaryLookup.getDeclaration returning null for "+new String(binding.declaringClass.qualifiedSourceName())+"."+new String(binding.constantPoolName())); //$NON-NLS-1$ //$NON-NLS-2$
			return null;
		}
		return findMatchingMethod(binding, type.methods);
	}
	public static FieldDeclaration getDeclaration(FieldBinding binding, BinaryTypeBinding binaryTypeBinding) {
		// Should be safe to set needResolve to true in next call:
		FieldBinding bindingFromDeclaringClass = binaryTypeBinding.getField(binding.name, /*needResolve*/true);
		if(bindingFromDeclaringClass.fieldDeclaration != null) {
			return bindingFromDeclaringClass.fieldDeclaration;
		}
		TypeDeclaration type = binaryTypeBinding.typeDeclaration;
		if (type != null)
			return findMatchingField(binding, type.fields);
		// Write message to console: FIXME: should be reporting a problem ...
		// System.out.println("JmlBinaryLookup.getDeclaration returning null for "+new String(binding.declaringClass.qualifiedSourceName())+"."+new String(binding.name)); //$NON-NLS-1$ //$NON-NLS-2$
		return null;
	}
}
