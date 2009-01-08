package org.jmlspecs.jml4.fspv;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.DefaultCompilerExtension;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.fspv.theory.Theory;
import org.jmlspecs.jml4.util.Logger;

public class Fspv extends DefaultCompilerExtension {

	public static boolean DEBUG = false;

	public String name() { return "JMLFSPV"; } //$NON-NLS-1$

	public void preCodeGeneration(Compiler compiler,
			CompilationUnitDeclaration unit) {
		if (DEBUG) {
			Logger.println(this + " - compiler.options.jmlEnabled:     "+compiler.options.jmlEnabled); //$NON-NLS-1$
			Logger.println(this + " - compiler.options.jmlDbcEnabled:  "+compiler.options.jmlDbcEnabled); //$NON-NLS-1$
			Logger.println(this + " - compiler.options.jmlThyEnabled:  "+compiler.options.jmlFspvEnabled); //$NON-NLS-1$
		}
		if (compiler.options.jmlEnabled && compiler.options.jmlDbcEnabled && compiler.options.jmlFspvEnabled) {
			this.comp(compiler, unit);
		}
	}
		
	private void comp(Compiler compiler, CompilationUnitDeclaration unit) {
		if (unit.compilationResult.hasSyntaxError
				|| unit.compilationResult.hasErrors()
				|| unit.hasErrors()) 
			return;

		// STEP 1: JML + Java AST into Theory AST
		TheoryTranslator v = new TheoryTranslator();
		unit.traverse(v, unit.scope);
		// STEP 2: Decorate Theory AST with pre-state information.
		PrestateDecorator pv = new PrestateDecorator();
		Theory theoryWithSideEffects = (Theory) v.theory.visit(pv);
		// STEP 3: Eliminate expressions with Side-Effects
		SideEffectHandler sev = new SideEffectHandler();
		Theory theoryWoutSideEffects = (Theory) theoryWithSideEffects.visit(sev);
		// STEP 4: Translate theory into Isabelle/Simpl
		SimplTranslator iv = new SimplTranslator();
		String theory = (String) theoryWoutSideEffects.visit(iv); // TODO: change this to theoryWout... once the visitor is implemented.
		System.out.println(theory);
	}

	public void optionsToBuffer(CompilerOptions options, StringBuffer buf) {
		buf.append("\n\t\t- FSPV: ").append(options.jmlFspvEnabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$
	}

	public void getOptionsMap(CompilerOptions options, Map optionsMap) {
		optionsMap.put(JmlCompilerOptions.OPTION_EnableJmlFspv, options.jmlFspvEnabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	}

	public void setOptionsMap(CompilerOptions options, Map optionsMap) {
		Object optionValue;
		if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableJmlFspv)) != null) {
				options.jmlFspvEnabled = CompilerOptions.ENABLED.equals(optionValue);
		}
	}

	public static String pretyPrintArray(Object [] a) {
		String s=""; //$NON-NLS-1$
		for(int i=0;i<a.length; i++) {
			s+=a[i].toString();
			s+=(i==a.length-1) ? "" : "\n" ; //$NON-NLS-1$ //$NON-NLS-2$
		}
		return s;
	}
}
