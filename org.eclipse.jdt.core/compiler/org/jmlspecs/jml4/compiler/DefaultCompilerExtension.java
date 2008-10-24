package org.jmlspecs.jml4.compiler;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;

public abstract class DefaultCompilerExtension implements ICompilerExtension {

	public int configureArgs(String currentArg, String[] args, int index, Map options) {
		return ARG_NOT_HANDLED;
	}
	
	public void getOptionsMap(CompilerOptions options, Map optionsMap) {
		/* do nothing */
	}

	public boolean handleWarningToken(String token, boolean isEnabling, Map optionsMap) {
		return false;
	}

	public void initCompilerOptions(CompilerOptions options) {
		/* do nothing */
	}

	public String name() {
		return "DefaultCompilerExtension"; //$NON-NLS-1$
	}

	public String optionKeyFromIrritant(long irritant) {
		return null;
	}

	public abstract void optionsToBuffer(CompilerOptions options, StringBuffer buf);

	public void preCodeGeneration(Compiler compiler, CompilationUnitDeclaration unit) {
		/* do nothing */
	}

	public void setOptionsMap(CompilerOptions options, Map optionsMap) {
		/* do nothing */
	}

	public String warningTokenFromIrritant(long irritant) {
		return null;
	}

	public long warningTokenToIrritant(String token) {
		return 0;
	}

}
