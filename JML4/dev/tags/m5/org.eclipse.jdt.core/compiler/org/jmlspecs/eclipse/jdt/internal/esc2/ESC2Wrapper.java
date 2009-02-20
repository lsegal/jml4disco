package org.jmlspecs.eclipse.jdt.internal.esc2;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.batch.Main;
import org.eclipse.jdt.internal.compiler.env.INameEnvironment;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.core.builder.NameEnvironment;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;
import org.jmlspecs.jml4.compiler.DefaultCompilerExtension;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;

public class ESC2Wrapper extends DefaultCompilerExtension {

    public ESC2Wrapper() { /*empty*/ }
    
    public String name() { return "JMLESC2"; } //$NON-NLS-1$

    // This is the callback method. */
    public void preCodeGeneration(Compiler compiler, CompilationUnitDeclaration unit) {
        if (compiler.options.jmlEnabled && compiler.options.jmlEsc2Enabled) {
            comp(compiler,unit);
        }
    }

    /** Translates the filename received from the compiler into a form suitable
     * for error messages.  In this case of a command-line tool, the filename
     * is suitable as it stands.
     * @param filename the name of the file being compiled
     * @return the name of the file as used in error messages
     */
    protected String translatePath(String filename) {
        return filename;
    }
    
    protected String fileName;	// Absolute path of file to be ESCed.
    protected String [] args;	// Arguments to ESC/Java2.
    
    /**
     * Handle the pre-compilation tasks such as obtaining the absolute filename and seting the
     * argument list to be passed to the ESC compiler.
     * @param compiler the Eclipse compiler doing the JDT work, used to get values of compiler options
     * @param unit unit the file being compiled
     * @return 1 the process should continue to the ESC compiler or 0 if it should not.
     */
    private boolean precomp(Compiler compiler, CompilationUnitDeclaration unit) {

    	// javafe.util.ErrorSet.setReporter(compiler.problemReporter);
        // javafe.util.ErrorSet.setReporter(new EscjavaMarker.ProblemReporter());

        // Figure out the full-path of the file as denoted by unit - we need to do this because
        // the manner ESC is integrated it requires a file.  When we use the JDT AST we will not need
        // to make such a distinction.  
        // There are three cases:
        // 1) Within eclipse unit.getFileName() retrieves the path relative to the workspace
        // 2) Within a junit test unit.getFileName() we just obtain the filename - support for junit
        //    tests when we start using JDT's AST.
        // 3) Within the batch compiler unit.getFileName() returns the path relative to the CWD 
        //    the batch compiler was used.
        // Filename of compilation unit. NOTE: name is relative to work-space 
        // in UI mode or to CWD in batch mode.
        this.fileName = new String(unit.getFileName());

        this.fileName = translatePath(this.fileName);
        // FIXME: this test is only done so that we can skip ESC for all of JDT's junit
        // tests.  I am not sure why this fails considering we have a path and a workspace
        // i.e. /home/karabot/dev/workspaces/junit-workspace/Project1/src/p2/X.java
        if(this.fileName.indexOf("junit-workspace")!= -1) //$NON-NLS-1$
        	return false;
        else {
        	// FIXME: there are times (last seen in July, not sure whether the eclipse
        	// folks changed something so this may not be needed any longer) that 
        	// no workspace is obtained and the unit.getFileName() call does not return
        	// an absolute path, in this cases we should skip ESC as well.
        	File f = new File(this.fileName);
        	if(!f.exists()) // possible junit test - is there any other case?
        		return false;
        }       
        
        // FIXME: We temporarily skip the javafe.ast.PrimitiveType because it gets into what 
        //        it seems is an infinite loop.
        String fs = File.separator;
        if( this.fileName.endsWith("javafe" + fs + "ast" + fs + "PrimitiveType.java") )  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
            return false;
             
        String s = compiler.options.jmlSimplifyPath;
        if (s.length() > 0) {
            System.setProperty("simplify", s); //$NON-NLS-1$
        }

        setupArgs(compiler, this.fileName);
        
        return true;
    	
    }
    
    /** A method to initiate the work of the compiler
     * @param compiler the Eclipse compiler doing the JDT work, used to get values of compiler options
     * @param unit the file being compiled
     * @return the exit code from the ESC analysis
     */
    protected int comp(Compiler compiler, CompilationUnitDeclaration unit) {
    	int exitCode = 0;
    	if (this.precomp(compiler, unit)) {
            javafe.util.ErrorSet.setReporter(new Esc2ProblemReporter(compiler, unit));
    		exitCode = escjava.Main.compile(this.args);
    	}
    	return exitCode;
    }

    //@ modifies this.args;
    private void setupArgs(Compiler compiler, String fileName) {
    	boolean verbose = compiler.options.jmlEsc2EchoOutputEnabled; 

    	String classPath = getClassPath(compiler);
		String jmlSpecPath = compiler.options.jmlSpecPath.trim();
		if (verbose) Log.log(name() + ": SPECS = " + jmlSpecPath); //$NON-NLS-1$
		if (verbose) Log.log(name() + ": CLASSPATH = " + classPath); //$NON-NLS-1$
		if (verbose) Log.log(name() + ": FILE: " + this.fileName); //$NON-NLS-1$

    	List/*<String>*/ argsList = new ArrayList/*<String>*/();
       	/* Always start the argument list with defaults for -specs and
		 * -classpath. If the user supplies these arguments as well, then these
		 * defaults will be ignored (i.e. ESC/Java2 uses the last occurrences of
		 * -specs, etc).
		 */
    	if (!jmlSpecPath.equals("")) { //$NON-NLS-1$
    		argsList.add("-specs"); argsList.add(jmlSpecPath); //$NON-NLS-1$
    	}
    	if (!classPath.equals("")) { //$NON-NLS-1$
    		argsList.add("-classpath"); argsList.add(classPath); //$NON-NLS-1$
    	}
       	if (!verbose) {
       		argsList.add("-Quiet"); //$NON-NLS-1$
       	}
       	// Process user supplied command line arguments, if any.
       	String cmdLineArgs = compiler.options.jmlEsc2CommandLineArgs.trim();
    	if (!cmdLineArgs.equals("")) { //$NON-NLS-1$
			argsList.addAll(Arrays.asList(Main.tokenize(cmdLineArgs)));
    	}
       	argsList.add(fileName);
       	// if (verbose) Log.log(name() + ": args = " + argsList); //$NON-NLS-1$
       	this.args = (String[]) argsList.toArray(new String[0]);
    }

    // FIXME - can we get this info without accessing internal classes?
    /** Returns the classpath used for finding classes being analyzed by
     * the ESC tool, not the system classpath being used to run the Java application.
     * @param compiler the Eclipse JDT compiler that is calling this wrapper
     * @return the class path as it would be put in a command-line, that is absolute
     *   directory or jar file names separated by the platform's path separator
     */
    protected String getClassPath(Compiler compiler) {
        INameEnvironment ine = compiler.lookupEnvironment.nameEnvironment;
        String classPath = null;
        if (ine instanceof NameEnvironment) {
            NameEnvironment ne = (NameEnvironment) ine;
            // Need this to have all the java files on the path
            for (int i = 0; i < ne.getSourcePath().length; i++) {
                classPath = (classPath == null) ? ne.getSourcePath()[i]
                        : classPath + java.io.File.pathSeparator
                                + ne.getSourcePath()[i];
            }
            // Need this to get all the libraries, but also get all the .class files
            for (int i = 0; i < ne.getClasspath().length; i++) {
                classPath = (classPath == null) ? ne.getClasspath()[i]
                        : classPath + java.io.File.pathSeparator
                                + ne.getClasspath()[i];
            }
        }
        if (compiler.options.jmlEsc2EchoOutputEnabled){
        	if (Log.on) Log.log("ClassPath: " + classPath); //$NON-NLS-1$
        }
        return classPath == null ? "" : classPath; //$NON-NLS-1$
    }

    //-----------------------------------------------------------------------
    // ICompilerExtension methods:
    
    public int configureArgs(String currentArg, String[] args1, int index, Map options) {
		if (currentArg.equals("-esc2")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_EnableJml,
					CompilerOptions.ENABLED);
			options.put(JmlCompilerOptions.OPTION_EnableJmlEsc2,
					CompilerOptions.ENABLED);
			return index;
		}
		return ARG_NOT_HANDLED;
	}

	public void getOptionsMap(CompilerOptions options, Map optionsMap) {
	    optionsMap.put(JmlCompilerOptions.OPTION_EnableJmlEsc2, options.jmlEsc2Enabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	    optionsMap.put(JmlCompilerOptions.OPTION_EnableEsc2EchoOutput, options.jmlEsc2EchoOutputEnabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	    optionsMap.put(JmlCompilerOptions.OPTION_JmlEsc2CommandLineArgs, options.jmlEsc2CommandLineArgs);
	}

	public void setOptionsMap(CompilerOptions options, Map optionsMap) {
	    Object optionValue;
		if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableJmlEsc2)) != null) {
	    	options.jmlEsc2Enabled = CompilerOptions.ENABLED.equals(optionValue);
	    }
		if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableEsc2EchoOutput)) != null) {
	    	options.jmlEsc2EchoOutputEnabled = CompilerOptions.ENABLED.equals(optionValue);
	    }
		if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_JmlEsc2CommandLineArgs)) instanceof String) {
	        options.jmlEsc2CommandLineArgs = (String) optionValue;
	    }
	}

	public void optionsToBuffer(CompilerOptions options, StringBuffer buf) {
		buf.append("\n\t\t- ESC2:").append(options.jmlEsc2Enabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$
	    buf.append("\n\t\t\t- echo output: ").append(options.jmlEsc2EchoOutputEnabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$
	    buf.append("\n\t\t\t- command line args: ").append(options.jmlEsc2CommandLineArgs); //$NON-NLS-1$
	    buf.append("\n\t\t\t- simplify path: ").append(options.jmlSimplifyPath); //$NON-NLS-1$
	}

}