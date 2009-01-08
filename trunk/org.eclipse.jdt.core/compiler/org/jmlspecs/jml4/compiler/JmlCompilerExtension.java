/**
 * The main JML4 compiler extension.
 */
package org.jmlspecs.jml4.compiler;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.eclipse.jdt.internal.esc2.EscJava2Wrapper;
import org.jmlspecs.jml2.checker.JML2CheckerWrapper;
import org.jmlspecs.jml2.compiler.JML2CompilerWrapper;
import org.jmlspecs.jml4.esc.Esc;
import org.jmlspecs.jml4.fspv.Fspv;

public class JmlCompilerExtension extends DefaultCompilerExtension {

	public static void addDependentExtensions() {
    	// TODO: [PC] might it be possible to add the following
    	// only if the corresponding feature is enabled?
    	// (Maybe if we move this init into the 
    	// JmlCompilerExtension initCompilerOptions?
    	CompilerExtensionManager.addExtension(new Esc());
    	CompilerExtensionManager.addExtension(new Fspv());
    	CompilerExtensionManager.addExtension(new JML2CheckerWrapper());
    	CompilerExtensionManager.addExtension(new JML2CompilerWrapper());
    	// CompilerExtensionManager.addExtension(new Esc2CompilerExtension());
    	CompilerExtensionManager.addExtension(new EscJava2Wrapper());
	}

	public void initCompilerOptions(CompilerOptions o) {
		// Set options that are errors by default.
		o.errorThreshold |= 0; // i.e. currently there are none.
		// Set options that are warnings by default.
		o.warningThreshold |= JmlCompilerOptions.ReportNonNullTypeSystem;
		o.warningThreshold |= JmlCompilerOptions.ReportJmlCommentDisabled;
	}

	public String name() {
		return "JmlCompilerExtension"; //$NON-NLS-1$
	}

	public int configureArgs(String currentArg, String[] args, int index, Map options) {
		if (currentArg.equals("-specs")) { //$NON-NLS-1$
			index++;
			if (index >= args.length) {
				// TOO MANY
			} else {
				// ??? = args[index];
				options.put(JmlCompilerOptions.OPTION_SpecPath, args[index]);
			}
			return index;
		}
		if (currentArg.equals("-nullable")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_DefaultNullity,
					JmlCompilerOptions.NULLABLE);
			return index;
		}
		if (currentArg.equals("-dbc")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_EnableJml,
					CompilerOptions.ENABLED);
			options.put(JmlCompilerOptions.OPTION_EnableJmlDbc,
					CompilerOptions.ENABLED);
			return index;
		}
		if (currentArg.equals("-rac")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_EnableJml,
					CompilerOptions.ENABLED);
			options.put(JmlCompilerOptions.OPTION_EnableRac,
					CompilerOptions.ENABLED);
			return index;
		}
		if (currentArg.equals("-jml")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_EnableJml,
					CompilerOptions.ENABLED);
			return index;
		}
		if (currentArg.equals("-counts")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_EnableCounts,
					CompilerOptions.ENABLED);
			return index;
		}
		if (currentArg.equals("-explicitNullity")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_ExplicitNullityAnnotations,
					CompilerOptions.ENABLED);
			return index;
		}
		if (currentArg.equals("-esc")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_EnableJml,
					CompilerOptions.ENABLED);
			options.put(JmlCompilerOptions.OPTION_EnableJmlEsc,
					CompilerOptions.ENABLED);
			return index;
		}
		if (currentArg.equals("-newLoopSemantics")) { //$NON-NLS-1$
			options.put(JmlCompilerOptions.OPTION_EnableJml,
					CompilerOptions.ENABLED);
			options.put(JmlCompilerOptions.OPTION_EnableJmlNewLoopSemantics,
					CompilerOptions.ENABLED);
			return index;
		}
		return super.configureArgs(currentArg, args, index, options);
	}

	public boolean handleWarningToken(String token, boolean isEnabling, Map optionsMap) {
	    if (token.equals("nnts")) { //$NON-NLS-1$
	        optionsMap.put(
	                JmlCompilerOptions.OPTION_ReportNonNullTypeSystem,
	                isEnabling ? CompilerOptions.WARNING : CompilerOptions.IGNORE);
	    } else if (token.equals("explicitNullity")) { //$NON-NLS-1$
	        optionsMap.put(
	                JmlCompilerOptions.OPTION_ExplicitNullityAnnotations,
	                isEnabling ? CompilerOptions.WARNING : CompilerOptions.IGNORE); 
	
	    } else {
	        return false;
	    }
	    return true;
	}

	public void getOptionsMap(CompilerOptions options, Map optionsMap) {
	    optionsMap.put(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem, options.getSeverityString(JmlCompilerOptions.ReportNonNullTypeSystem));
	    optionsMap.put(JmlCompilerOptions.OPTION_ReportJmlCommentDisabled, options.getSeverityString(JmlCompilerOptions.ReportJmlCommentDisabled));
	    optionsMap.put(JmlCompilerOptions.OPTION_ExplicitNullityAnnotations, options.getSeverityString(JmlCompilerOptions.ReqExplicitNullityAnnotations));
	    optionsMap.put(JmlCompilerOptions.OPTION_DefaultNullity, options.jmlDefaultIsNonNull ? JmlCompilerOptions.NON_NULL : JmlCompilerOptions.NULLABLE);
	    optionsMap.put(JmlCompilerOptions.OPTION_EnableRac, options.jmlRacEnabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	    optionsMap.put(JmlCompilerOptions.OPTION_EnableCounts, options.jmlNullityCountsEnabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	    optionsMap.put(JmlCompilerOptions.OPTION_SpecPath, options.jmlSpecPath);
	    optionsMap.put(JmlCompilerOptions.OPTION_EnableJml, options.jmlEnabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	    optionsMap.put(JmlCompilerOptions.OPTION_EnableJmlDbc, options.jmlDbcEnabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	    optionsMap.put(JmlCompilerOptions.OPTION_EnableJmlEsc, options.jmlEscEnabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	    optionsMap.put(JmlCompilerOptions.OPTION_SimplifyPath, options.jmlSimplifyPath);
	    optionsMap.put(JmlCompilerOptions.OPTION_EscProverStrategy, options.jmlEscProverStrategy);
	    optionsMap.put(JmlCompilerOptions.OPTION_EscDistributedPropertiesFile, options.jmlEscDistributedPropertiesFile);
		optionsMap.put(JmlCompilerOptions.OPTION_EnableJmlNewLoopSemantics, options.jmlNewLoopSemanticsEnabled ? CompilerOptions.ENABLED: CompilerOptions.DISABLED);
	}

	public void setOptionsMap(CompilerOptions options, Map optionsMap) {
	    Object optionValue;
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_ReportNonNullTypeSystem)) != null) options.updateSeverity(JmlCompilerOptions.ReportNonNullTypeSystem, optionValue);
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_ReportJmlCommentDisabled)) != null) options.updateSeverity(JmlCompilerOptions.ReportJmlCommentDisabled, optionValue);     
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_ExplicitNullityAnnotations)) != null) options.updateSeverity(JmlCompilerOptions.ReqExplicitNullityAnnotations, optionValue);      
	
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_SpecPath)) instanceof String) {
	        options.jmlSpecPath = (String) optionValue;
	    }
	    // default nullity
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_DefaultNullity)) != null) {
	            options.jmlDefaultIsNonNull = JmlCompilerOptions.NON_NULL.equals(optionValue);
	    }
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableRac)) != null) {
	            options.jmlRacEnabled = CompilerOptions.ENABLED.equals(optionValue);
	    }
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableCounts)) != null) {
	            options.jmlNullityCountsEnabled = CompilerOptions.ENABLED.equals(optionValue);
	    }
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableJml)) != null) {
	    	options.jmlEnabled = CompilerOptions.ENABLED.equals(optionValue);
	    }
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableJmlDbc)) != null) {
	    	options.jmlDbcEnabled = CompilerOptions.ENABLED.equals(optionValue);
	    }
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableJmlEsc)) != null) {
	    	options.jmlEscEnabled = CompilerOptions.ENABLED.equals(optionValue);
	    }
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EscProverStrategy)) != null) {
	    	options.jmlEscProverStrategy = (String)optionValue;
	    }
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EscDistributedPropertiesFile)) != null) {
	    	options.jmlEscDistributedPropertiesFile = (String)optionValue;
	    }
	    if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_SimplifyPath)) instanceof String) {
	    	options.jmlSimplifyPath=(String) optionValue;
	    }
		if ((optionValue = optionsMap.get(JmlCompilerOptions.OPTION_EnableJmlNewLoopSemantics)) != null) {
			options.jmlNewLoopSemanticsEnabled = CompilerOptions.ENABLED.equals(optionValue);
		}
	}

	public void optionsToBuffer(CompilerOptions options, StringBuffer buf) {
	    buf.append("\n\t+ JML4: ").append(options.jmlEnabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$
	    buf.append("\n\t\t- DBC: ").append(options.jmlDbcEnabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$
	    buf.append("\n\t\t- prover strategy: ").append(options.jmlEscProverStrategy); //$NON-NLS-1$
	    buf.append("\n\t\t- distributed properties: ").append(options.jmlEscDistributedPropertiesFile); //$NON-NLS-1$
	    buf.append("\n\t\t- new loop semantics: ").append(options.jmlNewLoopSemanticsEnabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$
	    buf.append("\n\t\t- spec path: ").append(options.jmlSpecPath); //$NON-NLS-1$
	    buf.append("\n\t\t- report inadvertent annotation disabling: ").append(options.getSeverityString(JmlCompilerOptions.ReportJmlCommentDisabled)); //$NON-NLS-1$
	    buf.append("\n\t\t- nnts"); //$NON-NLS-1$
	    buf.append("\n\t\t\t- report non-null type system problems: ").append(options.getSeverityString(JmlCompilerOptions.ReportNonNullTypeSystem)); //$NON-NLS-1$
	    buf.append("\n\t\t\t- default nullity: ").append(options.jmlDefaultIsNonNull ? JmlCompilerOptions.NON_NULL : JmlCompilerOptions.NULLABLE); //$NON-NLS-1$    
	    buf.append("\n\t\t\t- count nullities: ").append(options.jmlNullityCountsEnabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$	
	    buf.append("\n\t\t\t\t- require explicity nullity annotations: ").append(options.getSeverityString(JmlCompilerOptions.ReqExplicitNullityAnnotations)); //$NON-NLS-1$   
	    buf.append("\n\t\t- RAC: ").append(options.jmlRacEnabled ? CompilerOptions.ENABLED : CompilerOptions.DISABLED); //$NON-NLS-1$
	}

	public String optionKeyFromIrritant(long irritant) {
		switch ((int) (irritant >>> 32)) {
		case (int) (JmlCompilerOptions.ReportNonNullTypeSystem >>> 32):
			return JmlCompilerOptions.OPTION_ReportNonNullTypeSystem;
		case (int) (JmlCompilerOptions.ReqExplicitNullityAnnotations >>> 32):
			return JmlCompilerOptions.OPTION_ExplicitNullityAnnotations;
		}
		return null;
	}

	public String warningTokenFromIrritant(long irritant) {
	    switch ((int)(irritant>>>32)) {
	        case (int) (JmlCompilerOptions.ReportNonNullTypeSystem >>> 32) :
	            return "nnts"; //$NON-NLS-1$
	        case (int) (JmlCompilerOptions.ReqExplicitNullityAnnotations >>> 32) :
	            return "explicitNullity"; //$NON-NLS-1$
	    }
	    return null;
	}

	public long warningTokenToIrritant(String warningToken) {
	    if ("nnts".equals(warningToken)) //$NON-NLS-1$
	        return JmlCompilerOptions.ReportNonNullTypeSystem | CompilerOptions.NullReference | CompilerOptions.PotentialNullReference;
	    if ("explicitNullity".equals(warningToken)) //$NON-NLS-1$
	            return JmlCompilerOptions.ReqExplicitNullityAnnotations;
	    return 0;
	}

}
