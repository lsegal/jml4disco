// <jml-start id="extensions" />
// @author David Cok
// @date 10 September 2007
// @author P.Chalin et al.
// This class is part of the JML4 extensions to JDT.

package org.jmlspecs.jml4.compiler;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.batch.Main;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;

/** This class is experimental.
 *  It is intended as a public API used in extending the JDT compiler.
 */
public class CompilerExtensionManager {
    
    static private final Map extensions = new HashMap();
    
    static {
    	addExtension(new JmlCompilerExtension());
    	JmlCompilerExtension.addDependentExtensions();
    }

    static public void addExtension(ICompilerExtension e) {
        extensions.put(e.name(),e);
    }
    
    static public Collection getExtensions() {
        return extensions.values();
    }
    
    static public void runJDTCompiler(String[] args) {
        //org.eclipse.jdt.internal.compiler.batch.Main.main(args);
        // We use the line below rather than the line above so that we can prevent
        // the compiler from calling System.exit when it is finished.  At this
        // writing the line below is simply the content of the line above.
        Main c = new org.eclipse.jdt.internal.compiler.batch.Main(new PrintWriter(System.out), new PrintWriter(System.err), false, /*customDefaultOptions*/null, /*progress*/null);
        c.compile(args);
    }
    
    static public void preCodeGeneration(Compiler compiler, CompilationUnitDeclaration unit) {
        if (extensions == null) return;
        Iterator iter = extensions.values().iterator();
        while (iter.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)iter.next();
            e.preCodeGeneration(compiler,unit);
        }
        return;
    }

    static public void initCompilerOptions(CompilerOptions options) {
        if (extensions == null) return ;
        Iterator i = extensions.values().iterator();
        while (i.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)i.next();
            e.initCompilerOptions(options);
        }
        return;
    }

    static public int configureArgs(String currentArg, String[] newCommandLineArgs, int index, Map options) {
        if (extensions == null) return index-1;
        Iterator iter = extensions.values().iterator();
        while (iter.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)iter.next();
            int i = e.configureArgs(currentArg,newCommandLineArgs,index,options);
            if (i >= index) {
                return i;
            }
        }
        return IBatchCompilerExtension.ARG_NOT_HANDLED;
    }

    static public boolean handleWarningToken(String token, boolean isEnabling, Map optionsMap) {
        if (extensions == null) return false;
        Iterator i = extensions.values().iterator();
        while (i.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)i.next();
            if (e.handleWarningToken(token,isEnabling,optionsMap)) return true;
        }
        return false;
    }
    
    static public boolean getOptionsMap(CompilerOptions options, Map optionsMap) {
        if (extensions == null) return false;
        Iterator i = extensions.values().iterator();
        while (i.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)i.next();
            e.getOptionsMap(options,optionsMap);
        }
        return false;
    }
    
    static public void setOptionsMap(CompilerOptions options, Map optionsMap) {
        if (extensions == null) return ;
        Iterator i = extensions.values().iterator();
        while (i.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)i.next();
            e.setOptionsMap(options,optionsMap);
        }
        return ;
    }
    
    static public void optionsToBuffer(CompilerOptions options, StringBuffer buf) {
        if (extensions == null) return ;
        Iterator i = extensions.values().iterator();
        while (i.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)i.next();
            e.optionsToBuffer(options,buf);
        }
        return ;
    }
    
    public static String optionKeyFromIrritant(long irritant) {
        if (extensions == null) return null;
        Iterator i = extensions.values().iterator();
        while (i.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)i.next();
            String s = e.optionKeyFromIrritant(irritant);
            if (s != null) return s;
        }
        return null;
    }

    public static String warningTokenFromIrritant(long irritant) {
        if (extensions == null) return null;
        Iterator i = extensions.values().iterator();
        while (i.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)i.next();
            String s = e.warningTokenFromIrritant(irritant);
            if (s != null) return s;
        }
        return null;
    }
    
    public static long warningTokenToIrritant(String token) {
        if (extensions == null) return 0;
        Iterator i = extensions.values().iterator();
        while (i.hasNext()) {
            ICompilerExtension e = (ICompilerExtension)i.next();
            long irritant = e.warningTokenToIrritant(token);
            if (irritant != 0) return irritant;
        }
        return 0;
    }

}
//<jml-end id="extensions" />