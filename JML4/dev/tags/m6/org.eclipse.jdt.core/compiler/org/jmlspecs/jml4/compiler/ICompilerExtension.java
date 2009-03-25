// <jml-start id="extensions" />
// @author David Cok
// @date 10 September 2007
// @author P.Chalin et al.
// This class is part of the JML-ESC extensions to JDT with the JML4 architecture

package org.jmlspecs.jml4.compiler;

/** This class is experimental.
 *  It is intended as an interface used in extending the JDT compiler.
 */
import java.util.Map;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;

public interface ICompilerExtension extends IBatchCompilerExtension {
	
	/** @return user-friendly name of this compiler extension. */
    public String name();
    public void initCompilerOptions(CompilerOptions options);
    public void preCodeGeneration(Compiler compiler, CompilationUnitDeclaration unit);
    public void getOptionsMap(CompilerOptions options, Map optionsMap);
    public String optionKeyFromIrritant(long irritant);
    public void setOptionsMap(CompilerOptions options, Map optionsMap);
    public void optionsToBuffer(CompilerOptions options, StringBuffer buf);
    public String warningTokenFromIrritant(long irritant);
    public long warningTokenToIrritant(String token);
}
//<jml-end id="extensions" />