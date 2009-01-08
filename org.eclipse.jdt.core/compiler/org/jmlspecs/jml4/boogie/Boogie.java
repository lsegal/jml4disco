package org.jmlspecs.jml4.boogie;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.jml4.compiler.DefaultCompilerExtension;
import org.jmlspecs.jml4.util.Logger;

public class Boogie extends DefaultCompilerExtension {
	private static final boolean DEBUG = true;

	public String name() { return "JML4BOOGIE"; } //$NON-NLS-1$

	public void preCodeGeneration(Compiler compiler, CompilationUnitDeclaration unit) {
		if (DEBUG) {
			Logger.println(this + " - compiler.options.jmlEnabled:     "+compiler.options.jmlEnabled); //$NON-NLS-1$
			Logger.println(this + " - compiler.options.jmlBoogieEnabled:  "+compiler.options.jmlBoogieEnabled); //$NON-NLS-1$
		}
		if (compiler.options.jmlEnabled && compiler.options.jmlDbcEnabled && compiler.options.jmlBoogieEnabled) {
			process(compiler, unit);
		}
	}

	private void process(Compiler compiler, CompilationUnitDeclaration unit) {
		BoogieAdapter adapter = new BoogieAdapter(compiler);
		adapter.prove(unit);
	}

	public void optionsToBuffer(CompilerOptions options, StringBuffer buf) {
		buf.append("\n\t\t- BOOGIE: ").append(options.jmlBoogieEnabled ?  //$NON-NLS-1$
				CompilerOptions.ENABLED : CompilerOptions.DISABLED); 
	}

}
