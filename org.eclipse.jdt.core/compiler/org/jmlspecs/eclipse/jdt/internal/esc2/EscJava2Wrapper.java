package org.jmlspecs.eclipse.jdt.internal.esc2;
/**
 * @author George Karabotsos
 * @author David Cok
 * This class is part of the JML-ESC extensions to the JDT, under the JML4 architecture
 */

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;

public class EscJava2Wrapper extends ESC2Wrapper {

    public static boolean manualRun = false;
    
    // FIXME - this ought to be improved - it is not thread-safe, etc.
    // It is set by the CompilerParticipant.  Also it does not get reset
    public static IJavaProject currentProject;
    
    public EscJava2Wrapper() {
        // nothing
    }
    
    // This is the callback method. */
    public void preCodeGeneration(Compiler compiler, CompilationUnitDeclaration unit) {
        if (manualRun || (compiler.options.jmlEnabled && compiler.options.jmlEsc2Enabled)) {    
            comp(compiler,unit);
        }
    }
    
    /* (non-Javadoc)
     * @see org.jmlspecs.eclipse.jdt.core.EscJava2BatchWrapper#translatePath(java.lang.String)
     */
    // This implementation anticipates that fileName is a workspace-absolute
    // path and translates it into an absolute file system path suitable for ESCTools
    // FIXME test that this is correct if the file system path contains a link
    // FIXME should this use toOSString and use paths?  Does this work correctly on all platforms?
    protected String translatePath(String fileName) {
        IWorkspace workspace = ResourcesPlugin.getWorkspace();
        if(workspace != null) { // we got a workspace so it is safe to obtain its absolute location
        	IFile f = workspace.getRoot().getFile(new Path(fileName));	
            fileName = f.getRawLocation().toString();
        }
        return fileName;
    }
}
