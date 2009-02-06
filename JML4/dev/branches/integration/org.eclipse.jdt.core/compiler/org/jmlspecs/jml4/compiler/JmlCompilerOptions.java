package org.jmlspecs.jml4.compiler;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;


public class JmlCompilerOptions extends CompilerOptions {
	/**
	 * Option IDs
	 */
    public static final String OPTION_EnableJml = "org.eclipse.jdt.core.compiler.problem.enableJml"; //$NON-NLS-1$
    public static final String OPTION_EnableJmlNewLoopSemantics = "org.eclipse.jdt.core.compiler.problem.enableJmlNewLoopSemantics"; //$NON-NLS-1$    
    public static final String OPTION_ReportJmlCommentDisabled = "org.eclipse.jdt.core.compiler.problem.jmlCommentDisabled"; //$NON-NLS-1$ //[DSRG]
    public static final String OPTION_SpecPath = "org.eclipse.jdt.core.compiler.problem.specPath"; //$NON-NLS-1$
    //DBC
    public static final String OPTION_EnableJmlDbc = "org.eclipse.jdt.core.compiler.problem.enableJmlDbc"; //$NON-NLS-1$
    //ESC
    public static final String OPTION_EnableJmlEsc = "org.eclipse.jdt.core.compiler.problem.enableJmlEsc"; //$NON-NLS-1$   
    //NNTS
    public static final String OPTION_DefaultNullity = "org.eclipse.jdt.core.compiler.problem.defaultNullity"; //$NON-NLS-1$
    public static final String OPTION_ReportNonNullTypeSystem = "org.eclipse.jdt.core.compiler.problem.nonNullTypeSystem"; //$NON-NLS-1$ //[DSRG]
    public static final String OPTION_EnableCounts = "org.eclipse.jdt.core.compiler.problem.enableCounts"; //$NON-NLS-1$
    public static final String OPTION_ExplicitNullityAnnotations = "org.eclipse.jdt.core.compiler.problem.explicitNullityAnnotations"; //$NON-NLS-1$ //[DSRG]
    //RAC
    public static final String OPTION_EnableRac = "org.eclipse.jdt.core.compiler.problem.enableRac"; //$NON-NLS-1$
    // FSPV
  	public static final String OPTION_EnableJmlFspv = "org.eclipse.jdt.core.compiler.problem.enableJmlThy"; //$NON-NLS-1$
    // ESC2
    public static final String OPTION_EnableJmlEsc2 = "org.eclipse.jdt.core.compiler.problem.enableJmlEsc2"; //$NON-NLS-1$
    public static final String OPTION_JmlEsc2CommandLineArgs="org.eclipse.jdt.core.compiler.problem.JmlEsc2CommandLineArgs"; //$NON-NLS-1$
    public static final String OPTION_EnableEsc2EchoOutput="org.eclipse.jdt.core.compiler.problem.enableEsc2EchoOutput"; //$NON-NLS-1$
    public static final String OPTION_SimplifyPath = "org.eclipse.jdt.core.compiler.problem.simplifyPath"; //$NON-NLS-1$
    // JML2 Tool Integration
  	public static final String OPTION_EnableJml2Checker = "org.eclipse.jdt.core.compiler.problem.enableJml2Checker"; //$NON-NLS-1$
  	public static final Object OPTION_EnableJml2Compiler = "org.eclipse.jdt.core.compiler.problem.enableJml2Compiler"; //$NON-NLS-1$
  	// BOOGIE
    public static final String OPTION_EnableJmlBoogie = "org.eclipse.jdt.core.compiler.problem.enableJmlBoogie"; //$NON-NLS-1$   
  	// Distributed options
  	public static final String OPTION_EscProverStrategy = "org.eclipse.jdt.core.compiler.problem.jmlEscProverStrategy"; //$NON-NLS-1$
  	public static final String OPTION_EscDistributedPropertiesFile = "org.eclipse.jdt.core.compiler.problem.jmlEscDistributedPropertiesFile"; //$NON-NLS-1$
    
	/**
	 * Possible values for configurable options
	 */
    public static final String NULLABLE = "nullable"; //$NON-NLS-1$
    public static final String NON_NULL = "non_null"; //$NON-NLS-1$

	/**
	 * Bit mask for configurable problems (error/warning threshold)
	 *
	 * BEWARE: Keep an eye on the bits used by the JDT. Ensure that the
	 * bits used by JML are not also used by the JDT.
	 */
	public static final long ReportNonNullTypeSystem = ASTNode.Bit63L; 
	public static final long ReqExplicitNullityAnnotations = ASTNode.Bit64L;
	public static final long ReportJmlCommentDisabled = ASTNode.Bit62L; 
}
