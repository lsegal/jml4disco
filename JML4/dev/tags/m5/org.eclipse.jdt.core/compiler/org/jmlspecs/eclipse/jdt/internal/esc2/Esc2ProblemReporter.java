package org.jmlspecs.eclipse.jdt.internal.esc2;

import javafe.genericfile.GenericFile;
import javafe.util.ClipPolicy;
import javafe.util.ErrorSet;
import javafe.util.Location;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;

public class Esc2ProblemReporter extends ErrorSet.StandardReporter {
    private final /*@non_null*/ Compiler compiler;
    private final /*@non_null*/ CompilationUnitDeclaration unit;
    
    public Esc2ProblemReporter(Compiler compiler, CompilationUnitDeclaration unit) {
        this.compiler=compiler;
        this.unit=unit;
    }

    public void report(int severity, int loc, int length, String message) {
    	if (compiler.options.jmlEsc2EchoOutputEnabled) {
    		super.report(severity, loc, length, message);
    	}
        int sourceStart = 0;
        int sourceEnd = 0;
        String msg = "[esc2] "; //$NON-NLS-1$

        if (loc == javafe.util.Location.NULL) {
        	// do nothing more
        } else {
            // The following is the file reported in the error message
            // It is a file-system path name in native OS format
            String errorFileName = javafe.util.Location.toFileName(loc);
            // The following is the file being compiled
            String compFileName = new String(this.unit.getFileName());
            // Are they the same?
            IPath p = new Path(errorFileName).makeAbsolute(); // absolute file-system path
            IPath pp0 = new Path(compFileName); // path relative to the workspace root
            IResource resource = getRoot().findMember(pp0);
            IPath pp = resource.getLocation();
            boolean sameFile = p.equals(pp);
            if (!sameFile) {
                // Put filename in message, if it is a different file
                // msg += javafe.util.Location.toFileName(loc) + ":"; //$NON-NLS-1$
                // For now do not display these as problems ...
                return;
            } else if (!javafe.util.Location.isWholeFileLoc(loc)) {
            	sourceStart = javafe.util.Location.toOffset(loc) - 1;
            	sourceEnd = sourceStart + computeProblemLength(loc, length);
            }
            // msg += javafe.util.Location.toLineNumber(loc) + ":";
            msg += trim(message);
            this.report2(severity, sourceStart, sourceEnd, msg);
    	}
    }

    private String trim(String message) {
    	String[] prefixes = { "Warning: ", "Caution: ", "Error: " }; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
    	for(int i = 0; i < prefixes.length; i++) {
    		if (message.startsWith(prefixes[i])) {
    			return message.substring(prefixes[i].length());
    		}
    	}
    	return message;
	}

	/**
	 * In general, ESC/Java2 doesn't provide us with an accurate representation
	 * of the _end_ of the text for which a problem is being reported. This
	 * method returns <code>length</code> if it is positive otherwise the length
	 * from the column position of <code>loc</code> until the end of the same line.
	 */
    private int computeProblemLength(int loc, int length) {
		if (length > 0) {
			return length;
		}
		int lineStartOffset = Location.toOffset(loc);
		int line = javafe.util.Location.toLineNumber(loc);
		int nextLineLoc = Location.make(Location.toStreamId(loc), line+1, 0);
		int lineEndOffset = Location.toOffset(nextLineLoc - 1);
		return lineEndOffset - lineStartOffset;
	}

	private void report2(int severity, int sourceStart, int sourceEnd, String message) {
    	if (this.compiler != null && this.compiler.problemReporter.referenceContext == null) {
    		this.compiler.problemReporter.referenceContext = this.unit;
    	}
    	this.compiler.problemReporter.jmlEsc2Warning(message, sourceStart, sourceEnd);
	}

	public void reportAssociatedInfo(int loc) {
		// FIXME: re-enable.
    	if (true) return; 
    	
        if (loc == Location.NULL) return;

        String filename = null;
        int line = 0;
        int cpos = 0;
        if (Location.isWholeFileLoc(loc)) {
            GenericFile f = Location.toFile(loc);
            filename = f.getHumanName();
            if (f instanceof java.io.File) {
                filename = ((java.io.File)f).getAbsolutePath();
            }
        } else {
            GenericFile f = Location.toFile(loc);
            filename = f.getHumanName();
            if (f instanceof java.io.File) {
                filename = ((java.io.File)f).getAbsolutePath();
            }
            line = Location.toLineNumber(loc);
            cpos = Location.toOffset(loc);
        }

        IResource res = null;
        if (filename != null) {
            
            // FIXME - this works as long as the filename coming in
            // is a totally absolute file-system path name
            // Is it ever something else?  Can we tell and adjust using 
            // java system calls?
            // DOes it work when the file is linked? - e.g. specs files
            IPath filePath = new Path(filename);
            IFile ffile = /*UIUtils.*/getRoot().getFileForLocation(filePath);
            res = ffile;
            // TODO
//          if (res == null) {
//              // It is likely that filePath is an absolute path to
//              // a linked resource
//              IResource s = Utils.mapBack(JavaCore.create(resource.getProject()),file,false);
//              res = s != null ? s : resource;
//          }
        }
        
        if (Log.on) {
            Log.log("ASSOCIATED INFO " + filename + " " + line + " " + cpos); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
        }
        
//        try {
//            addMarkerInfo(filename,line,cpos);
//        } catch (CoreException e) {
//            Log.errorlog("Failed to associated info", e);
//        }
    }

    public void reportAssociatedInfo2(int loc, ClipPolicy cp) {
        reportAssociatedInfo(loc);
    }


    /**
     * @return The singleton IWorkspaceRoot for the workspace
     */
    public static IWorkspaceRoot getRoot() {
    	// FIXME: can workspace be null?
        return ResourcesPlugin.getWorkspace().getRoot();
    }

}
