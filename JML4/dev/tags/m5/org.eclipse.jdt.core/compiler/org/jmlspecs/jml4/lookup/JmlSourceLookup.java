package org.jmlspecs.jml4.lookup;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.UnsupportedEncodingException;

import org.eclipse.jdt.internal.compiler.CompilationResult;
import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.AbstractMethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.Argument;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.batch.CompilationUnit;
import org.eclipse.jdt.internal.compiler.env.ICompilationUnit;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.ast.JmlAstUtils;
import org.jmlspecs.jml4.ast.JmlTypeReference;
import org.jmlspecs.jml4.compiler.JmlConstants;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlSourceLookup {
	private static final boolean DEBUG = false;
	private final JmlFileFinder jmlFileFinder;
	private final Compiler compiler;
	private final String defaultEncoding;


	public JmlSourceLookup(Compiler compiler) {
		this.jmlFileFinder = new JmlFileFinder(compiler);
		this.compiler = compiler;
		this.defaultEncoding = (this.compiler.options.defaultEncoding == null)
								?	"ISO-8859-1" //$NON-NLS-1$;
								:	this.compiler.options.defaultEncoding;
	}
	public JmlFileFinder getJmlFileFinder() {
		return this.jmlFileFinder;
	}
	private void mergeWithSpec(CompilationUnitDeclaration unit) {
		if (unit.types == null || unit.types.length == 0 || unit.types[0] == null || unit.types[0].binding == null)
			return;
		String unitName = JmlAstUtils.concatWith(unit.types[0].binding.compoundName, File.separatorChar);
        File[] files = this.jmlFileFinder.findSpecs(unitName);
        merge(unit, unitName, files);
	}
	private void mergeWithSource(CompilationUnitDeclaration unit) {
		// FIXME: we will want to iterate over unit.types rather than only merge unit.types[0].
		if (unit.types == null || unit.types.length == 0 || unit.types[0] == null || unit.types[0].binding == null)
			return;
		String unitName = JmlAstUtils.concatWith(unit.types[0].binding.compoundName, File.separatorChar);
        File[] files = this.jmlFileFinder.findSource(unitName);
        merge(unit, unitName, files);
	}
	public void mergeWithSourceAndSpec(CompilationUnitDeclaration unit) {
		mergeWithSource(unit);
		mergeWithSpec(unit);
	}
	private void merge(CompilationUnitDeclaration unit, String unitName, File[] files) {
        if (DEBUG) System.out.println("JmlSourceLookup: found " + files.length + " file(s) for '" + new String(unitName)+JmlConstants.SQUOTE); //$NON-NLS-1$ //$NON-NLS-2$
        CompilationUnitDeclaration[] specs = this.parse(files);
        for (int i = 0; i < specs.length; i++) {
        	if (specs[i].types != null) {
				for (int j = 0; j < specs[i].types.length; j++) {
					TypeDeclaration spec = specs[i].types[j];
		    		merge(unit, spec);
				}
        	}
		}
	}

	//@ requires unit.scope != null;
	private void merge(CompilationUnitDeclaration unit, TypeDeclaration spec) {
		String specName = new String(spec.name);
        if (DEBUG) System.out.println("JmlSourceLookup: reading '" + specName +JmlConstants.SQUOTE); //$NON-NLS-1$
		for (int i = 0; i < unit.types.length; i++) {
			TypeDeclaration source = unit.types[i];
			String sourceName = new String(source.name);
			if (! sourceName.equals(specName))
				continue;
			merge(unit.scope.problemReporter(), source, spec);
		}
	}

	void merge(ProblemReporter problemReporter, TypeDeclaration source, TypeDeclaration spec) {
		mergeFields(source.fields, spec.fields);
		mergeMethods(problemReporter, source.methods, spec.methods);
		int length = source.memberTypes == null ? 0 : source.memberTypes.length;

		for (int i = 0; i < length; i++) {
			if (spec.memberTypes != null && i < spec.memberTypes.length && new String(spec.memberTypes[i].name).equals(new String(source.memberTypes[i].name))) {
				merge(problemReporter, source.memberTypes[i], spec.memberTypes[i]);
			} else if (spec.memberTypes != null && i < spec.memberTypes.length && ! (new String(spec.memberTypes[i].name).equals(new String(source.memberTypes[i].name)))) {
				String msg = "member types [" + i //$NON-NLS-1$
						+ "] don't match for type '" //$NON-NLS-1$
						+ (new String(source.name)) + "': source(" //$NON-NLS-1$
						+ (new String(source.memberTypes[i].name))
						+ ") vs spec(" + (new String(spec.memberTypes[i].name)) //$NON-NLS-1$
						+ ")"; //$NON-NLS-1$
				problemReporter.jmlEsc2Error(msg, source.sourceStart(), source.sourceEnd());
			}
		}
	}

	private void mergeMethods(ProblemReporter problemReporter, AbstractMethodDeclaration[] sourceMethods, AbstractMethodDeclaration[] specMethods) {
		if (specMethods == null)
			return;
		for (int i = 0; i < sourceMethods.length; i++) {
			AbstractMethodDeclaration sourceMethod = sourceMethods[i]; 
			AbstractMethodDeclaration specMethod;
			if (i < specMethods.length && signaturesMatch(sourceMethod, specMethods[i])) 
				specMethod = specMethods[i];
			else
				specMethod = findMatchingMethod(sourceMethod, specMethods);
		    if (specMethod != null)
		    	mergeMethod(problemReporter, sourceMethod, specMethod);
		}
	}
	private void mergeMethod(ProblemReporter problemReporter, AbstractMethodDeclaration sourceMethod, AbstractMethodDeclaration specMethod) {
		if (new String(sourceMethod.selector).startsWith("\\")) { //$NON-NLS-1$
			// TODO: reexamine this if statement once all of JML is parsed
			return;
		}
		if (sourceMethod instanceof MethodDeclaration && specMethod instanceof MethodDeclaration)
           mergeMethodReturnType(problemReporter, (MethodDeclaration) sourceMethod, (MethodDeclaration) specMethod);
		
		if (sourceMethod.arguments != null)
           for (int i = 0; i < sourceMethod.arguments.length; i++) 
               mergeMethodParameter(sourceMethod.arguments[i], specMethod.arguments[i]);
	}
	/*package*/ static void mergeMethodReturnType(ProblemReporter problemReporter, MethodDeclaration sourceDecl, MethodDeclaration specDecl) {
		if(!(sourceDecl.returnType instanceof JmlTypeReference
				&& specDecl.returnType   instanceof JmlTypeReference)) {
			return;
		}
		Nullity sourceNullity = ((JmlTypeReference) sourceDecl.returnType).getNullity();
		Nullity specNullity   = ((JmlTypeReference) specDecl.returnType).getNullity();
		
		if (sourceNullity.hasExplicitNullity() && specNullity.hasExplicitNullity() && sourceNullity != specNullity) {
			String msg = "Nullity of declaration is different in specification file ("  //$NON-NLS-1$
				+ specNullity + ")"; //$NON-NLS-1$
			problemReporter.jmlEsc2Warning(msg, sourceDecl.sourceStart, sourceDecl.sourceEnd());
		} 
		int sourceStart = sourceDecl.returnType.sourceStart;
		int sourceEnd   = sourceDecl.returnType.sourceEnd;
		sourceDecl.returnType = specDecl.returnType;
		sourceDecl.returnType.sourceStart = sourceStart;
		sourceDecl.returnType.sourceEnd   = sourceEnd;
    }
	static void mergeMethodParameter(Argument sourceArg, Argument specArg) {
    	if (!(sourceArg.type instanceof JmlTypeReference
    			&& specArg.type instanceof JmlTypeReference)) {
    		return;
    	}

		Nullity sourceNullity = ((JmlTypeReference) sourceArg.type).getNullity();
		Nullity specNullity   = ((JmlTypeReference) specArg.type).getNullity();
		
		if (sourceNullity.hasExplicitNullity() && specNullity.hasExplicitNullity() && sourceNullity != specNullity) {
		   System.out.println("issue warning: nullities don't match for method param '"+(new String(sourceArg.name))+"' : source("+sourceArg.toString()+") vs spec("+specArg.toString()+")"); //TODO: report this problem //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		} 
		int sourceStart = sourceArg.type.sourceStart;
		int sourceEnd   = sourceArg.type.sourceEnd;
		sourceArg.type = specArg.type;
		sourceArg.type.sourceStart = sourceStart;
		sourceArg.type.sourceEnd   = sourceEnd;
	}
	private static /*@nullable*/ AbstractMethodDeclaration findMatchingMethod(AbstractMethodDeclaration sourceMethod, AbstractMethodDeclaration[] specMethods) {
		for (int i = 0; i < specMethods.length; i++) {
			if (signaturesMatch(sourceMethod, specMethods[i]))
				return specMethods[i];
		}
		return null;
	}

	public static void attachMethodDeclsToMethodBindings(AbstractMethodDeclaration[] methodDecls) {
		if (methodDecls == null || methodDecls.length == 0)
			return;
		for (int i = 0; i < methodDecls.length; i++) {
			MethodBinding methodBinding = methodDecls[i].binding;
			if(methodBinding != null && methodBinding.methodDeclaration == null)
				methodBinding.methodDeclaration = methodDecls[i];
		}
	}

	private static void mergeFields(FieldDeclaration[] sourceFields, FieldDeclaration[] specFields) {
		for (int i = 0; sourceFields != null && i < sourceFields.length; i++) {
			FieldDeclaration sourceField = sourceFields[i];
			if (sourceField == null || sourceField.name == null) continue;
			String sourceFieldName = new String(sourceField.name);
		    FieldDeclaration specField;
		    if (specFields != null && i < specFields.length && specFields[i] != null
		     && specFields[i].name != null && sourceFieldName.equals(new String(specFields[i].name)))
		    	specField = specFields[i];
		    else
		    	specField = findField(specFields, sourceFieldName);
		    if (specField == null)
		    	continue;
		    
		    if(!(sourceField.type instanceof JmlTypeReference
		    		&& specField.type instanceof JmlTypeReference)) {
		    	continue;
		    }
            Nullity sourceNullity = ((JmlTypeReference) sourceField.type).getNullity();
            Nullity specNullity   = ((JmlTypeReference) specField.type).getNullity();
		
            if (sourceNullity.hasExplicitNullity() && specNullity.hasExplicitNullity() && sourceNullity != specNullity) {
               System.out.println("issue warning: nullities don't match for field '"+(new String(specField.name))+"' : source("+specField.toString()+") vs spec("+specField.toString()+")"); //TODO: report this problem //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
            } 
            int sourceStart = sourceField.type.sourceStart;
            int sourceEnd   = sourceField.type.sourceEnd;
            sourceField.type = specField.type;
            sourceField.type.sourceStart = sourceStart;
            sourceField.type.sourceEnd   = sourceEnd;
		}
	}		
	
	static FieldDeclaration findField(FieldDeclaration[] specFields, String sourceFieldName) {
		if(specFields != null) {
			for (int i = 0; i < specFields.length; i++) {
				if (specFields[i].name != null
						&& sourceFieldName.equals(new String(specFields[i].name)))
					return specFields[i];
			}
		}
		return null;
	}

	private static boolean signaturesMatch(AbstractMethodDeclaration sourceMethod, AbstractMethodDeclaration specMethod) {
		if (! new String(sourceMethod.selector).equals(new String(specMethod.selector)))
			return false;
		Argument[] sourceArgs = sourceMethod.arguments;
		Argument[] specArgs= specMethod.arguments;
		
		int sourceLength = sourceArgs == null ? 0 : sourceArgs.length; 
		int specLength   = specArgs   == null ? 0 : specArgs.length; 
		if (sourceLength != specLength)
			return false;
		for (int i = 0; i < sourceLength; i++) {
			// calculate the equivalent to the constantPoolName for each argument's type name.
			// usually the package information will NOT be available
			String sourceTypeName = JmlAstUtils.concatWith(sourceArgs[i].type.getTypeName(), JmlConstants.SLASH);
			String specTypeName = JmlAstUtils.concatWith(specArgs[i].type.getTypeName(), JmlConstants.SLASH);
			
            if (! sourceTypeName.equals(specTypeName))
    				return false;
		}
		return true;
	}
	/* package */ CompilationUnitDeclaration[] parse(File[] files) {
		CompilationUnitDeclaration[] result = new CompilationUnitDeclaration[files.length];
        for (int i = 0; i < files.length; i++) {
        	char[] contents = readFile(files[i], this.defaultEncoding);
        	String filename = null;
        	try { filename = files[i].getCanonicalPath(); }
        	catch(IOException ignored) {/*ignored*/}
        	if (filename != null) {
        		ICompilationUnit sourceUnit = new CompilationUnit(contents, filename, this.defaultEncoding);
        		result[i] = this.dietParse(sourceUnit);
        	}
		}
        return result;
	}
	
	/*package*/ CompilationUnitDeclaration dietParse(ICompilationUnit unit) {
    	CompilationResult compilationResult = new CompilationResult(unit, -1, -1, 0);
    	CompilationUnitDeclaration result = this.compiler.parser.dietParse(unit, compilationResult);
    	return result;
	}
	
	// FIXME: is there not code elsewhere that achieves the same effect?
	private static char[] readFile(File file, String encoding) {
		int fileLength = (int) file.length();
		StringBuffer result = new StringBuffer(fileLength > 10 ? fileLength : 10);
		Reader in = null;
		try {
			in = new InputStreamReader(new FileInputStream(file), encoding);
			int c;
			while ((c = in.read()) >= 0) {
				result.append((char)c);
			}
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
		} catch (IOException e) {
			// TODO Auto-generated catch block
		} finally {
			if (in != null) {
				try {
					in.close();
				} catch (IOException e) {
					//do nothing
				}
			}
		}
		return result.toString().toCharArray();
	}	
}
