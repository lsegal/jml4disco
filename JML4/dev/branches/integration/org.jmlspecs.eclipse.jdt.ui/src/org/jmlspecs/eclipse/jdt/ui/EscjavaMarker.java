/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Jul 30, 2004
 *
 */
package org.jmlspecs.eclipse.jdt.ui;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;

/**
 * This class manages a new type of marker for Esc/Java2 warnings.
 * 
 * @author David R. Cok
 * @deprecated - we have reverted to problem reporting via the JDT core.
 */
public class EscjavaMarker  {
	
	/** 
	 * The id that is also used in plugin.xml.
	 */
	final static public String ESCJAVA_MARKER_ID =
		Activator.PLUGIN_ID + ".escjavaWarningMarker";
	
	/** The id of the marker property that holds the 'associated declaration' information. */
	final static public String EXTRA_INFO = "declarationInfo";

	static public void report(IPath errorPath, int severity, int loc, int length, String message) {
        String filename = null;
        int line = 0;
        int cpos = 0;
//        if (loc == Location.NULL) {
//        } else if (Location.isWholeFileLoc(loc)) {
//            GenericFile f = Location.toFile(loc);
//            filename = f.getHumanName();
//            if (f instanceof java.io.File) {
//                filename = ((java.io.File)f).getAbsolutePath();
//            }
//        } else {
//            GenericFile f = Location.toFile(loc);
//            filename = f.getHumanName();
//            if (f instanceof java.io.File) {
//                filename = ((java.io.File)f).getAbsolutePath();
//            }
//            line = Location.toLineNumber(loc);
//            cpos = Location.toOffset(loc);
//        }

	    escjavaFailedX(
              null, // TODO - containing project?
              filename,
              line,
              cpos-1,
              length,
              message,
              IEscjavaListener.WARNING); // FIXME - how to translate errors?
	}

	/**
	 * A callback method called when a marker should be created.
	 * @param resource The resource in which the error occured
	 * @param file The file in which the error occured
	 * @param lineNumber The line number where the error happened
	 * @param offset The character position (0-based) from the beginning of the file where the error begins
	 * @param length The number of characters to highlight
	 * @param errorMessage A message explaining the type of error
	 * @param severity The severity of the error (using one of the error severity constants defined in this class)
	 */
     public void escjavaFailed(
            IResource resource,
            String file,
            int lineNumber,
            int offset,
            int length,
            String errorMessage,
            final int severity) {
        // TODO ???
         
     }
     
     static public void escjavaFailedX(
                IResource resource,
                String file,
                int lineNumber,
                int offset,
                int length,
                String errorMessage,
                final int severity) {

		IResource res = null;
		if (file == null) {
			res = resource;
		} else {
			
			// FIXME - this works as long as the filename coming in
			// is a totally absolute file-system path name
			// Is it ever something else?  Can we tell and adjust using 
			// java system calls?
			// DOes it work when the file is linked? - e.g. specs files
			IPath filePath = new Path(file);
			IFile ffile = /*UIUtils.*/getRoot().getFileForLocation(filePath);
			res = ffile;
			// TODO
//			if (res == null) {
//				// It is likely that filePath is an absolute path to
//				// a linked resource
//				IResource s = Utils.mapBack(JavaCore.create(resource.getProject()),file,false);
//				res = s != null ? s : resource;
//			}
		}
		
		if (Log.on) {
            Log.log("MARKER " + file + " " + lineNumber + " " +
                    errorMessage);
		}
		
		final int finalLineNumber = lineNumber;
		final int finalOffset = offset;
		final int finalLength = length;
		final String finalErrorMessage = errorMessage;
		
		if (res == null) return;
		if (!res.exists()) return; // FIXME - this can happen for specs in jar files, even though they exist - what to do?
		try {
			final IResource r = res;
			// Eclipse recommends that things that modify the resources
			// in a workspace be performed in a IWorkspaceRunnable
			IWorkspaceRunnable runnable = new IWorkspaceRunnable() {
				public void run(IProgressMonitor monitor) throws CoreException {
					IMarker marker = r.createMarker(ESCJAVA_MARKER_ID);
					setMarkerAttributes(marker, finalLineNumber, finalOffset, finalLength, finalErrorMessage, severity);
					mostRecentMarker = marker;
				}
			};
			// Originally the following version of run was used:
			// 		r.getWorkspace().run(runnable, null);
			// It was replaced with the following and passed a null value for 
			// an instance of ISchedulingRule because the default one (workspace)
			// was resulting into a deadlock.
			// FIXME: Is this sufficient?  Could we be using 
			r.getWorkspace().run(runnable, null, IWorkspace.AVOID_UPDATE, null);
		} catch (CoreException e) {
			Log.errorlog("Unexpected exception while creating a Marker: ",e);
		}
	}
	
	/** A cache of the most recently produced marker, so that associated info
	 *  coming in subsequent jmlFailed calls can be associated with the correct marker.
	 */
	// FIXME - another reason this is not thread-safe
	private static IMarker mostRecentMarker = null;
	
	/**
	 * Sets the attributes of a marker.
	 * @param marker The marker whose attributes are to be set
	 * @param finalLineNumber The line to mark, beginning with 1; use 0 if no line should be marked.
	 * @param finalOffset The starting 0-based character number within the file to mark
	 * @param finalLength The length in characters of the error location.
	 * @param finalErrorMessage The message conveying relevant information
	 * @param severity The severity (values from IEscjavaListener).
	 * @throws JavaModelException
	 * @throws CoreException
	 */
	static private void setMarkerAttributes(IMarker marker, 
			int finalLineNumber, int finalOffset,
			int finalLength,
			String finalErrorMessage, int severity)
	throws JavaModelException, CoreException {
		mostRecentMarker = marker;
		if (finalLineNumber >= 1) {
			marker.setAttribute(IMarker.LINE_NUMBER, finalLineNumber);
		}
		if (finalOffset >= 0) {
			marker.setAttribute(IMarker.CHAR_START, finalOffset); 
			marker.setAttribute(IMarker.CHAR_END, finalOffset+(finalLength>0?finalLength:2));
		}
			// Note - it appears that CHAR_START is measured from the beginning of the
			// file and overrides the line number

		marker.setAttribute(IMarker.SEVERITY,
				severity == IEscjavaListener.ERROR ? IMarker.SEVERITY_ERROR :
					severity == IEscjavaListener.WARNING ? IMarker.SEVERITY_WARNING:
									IMarker.SEVERITY_INFO);
		marker.setAttribute(IMarker.MESSAGE, finalErrorMessage);
	}

	/**
	 * Adds extra information to the most recently 
	 * created marker
	 * 
	 * @param s The additional information to be added
	 * @throws CoreException
	 */
	//@ requires mostRecentMarkerInfo != null;
	static public void addMarkerInfo(String filename, int line, int cpos) throws CoreException {
	    if (mostRecentMarker == null) return;
		if (Log.on) Log.log("Adding extra marker info: " + filename + " " + line + " " + cpos);
		mostRecentMarker.setAttribute(IMarker.MESSAGE, mostRecentMarker.getAttribute(IMarker.MESSAGE) 
		        + "\nAssociated specification: " + filename + ", line " + line);
		Object o = mostRecentMarker.getAttribute(EXTRA_INFO);
		String a = o == null ? "" : ((String)o + ";");
		a = a + filename + " " + line + " " + cpos;
		mostRecentMarker.setAttribute(EXTRA_INFO,a);
	}
	
	/**
	 * A callback called when the set of markers should be cleared.
	 * 
	 * @param r The resource whose markers are to be cleared
	 * @throws CoreException
	 */
	static public void clearMarkers(IResource r) throws CoreException {
		if (r.exists()) r.deleteMarkers(ESCJAVA_MARKER_ID,
				false, IResource.DEPTH_INFINITE);
		// false above indicates not to delete subtypes.  
		// Perhaps it should be true, but there are no subtypes
		// defined right now.
	}

	/**
	 * Clears all the markers for the resources in the Collection; does
	 * this within a ResourcesPlugin batch operation
	 * 
	 * @param c A collection of IResource objects
	 * @throws CoreException
	 */
	public static void clearMarkers(final Collection c) throws CoreException {
		ResourcesPlugin.getWorkspace().run(
				new IWorkspaceRunnable() {
					public void run(IProgressMonitor pm) throws CoreException {
						Iterator i = c.iterator();
						while (i.hasNext()) {
							IResource r = (IResource)i.next();
							if (r.exists()) r.deleteMarkers(ESCJAVA_MARKER_ID, false, IResource.DEPTH_INFINITE);
						}
					}
				},null);
	}
	
	/**
	 * Returns the extra information associated with a Marker.
	 * @param m The marker whose infor is to be returned
	 * @return  A List of String containing associated locations
	 * @throws Exception
	 */
	//@ requires m != null;;
	//@ ensures \result != null;
	static public List getExtraInfo(IMarker m) throws Exception {
		List list = new LinkedList();
		String s = (String)m.getAttribute(EXTRA_INFO);
		//System.out.println("EX " + s);
		if (s == null) return list;
		// FIXME - use some sort of string parser
		int k;
		while ((k = s.indexOf(';')) != -1) {
			list.add(s.substring(0,k));
			s = s.substring(k+1);
		}
		list.add(s);
		return list;
	}
	
//	static class Provider implements IMarkerImageProvider {
//		public String getImagePath(IMarker marker) {
//			//System.out.println("CALLED");
//			return "icons/escjava_problem.gif";
//		}	
//	}
	
//	static public class ProblemReporter extends ErrorSet.StandardReporter {
//
//		//FIXME: Not sure what are the uses of the compiler and unit members, considering:
//		//       - they are no longer set.
//		//       - Dave's EscjavaMarker class seem to be doing a better job at adding markers.
//		//       - Could it be that they are needed for future enhancement when markers are inserted
//		//         in the different files?  Hence the code comparing the files below.
//		// [g_karab]
//	    Compiler compiler;
//	    CompilationUnitDeclaration unit;
//	    
//        public ProblemReporter(Compiler compiler, CompilationUnitDeclaration unit) {
//            // TODO Auto-generated constructor stub
//            this.compiler=compiler;
//            this.unit=unit;
//        }
//
//        public ProblemReporter() {
//            // TODO Auto-generated constructor stub
//            this.compiler=null;
//            this.unit=null;
//        }
//
//	    public void report(int severity, int loc, int length, String message) {
//	        mostRecentMarker = null; // Set this field to null in case no marker is produced
//	        super.report(severity, loc, length, message);
//	        if (loc == javafe.util.Location.NULL) {
//	            // The location of the error is unknown
//                // FIXME: Check for this.compiler nullity considering this will fail when compiler 
//                //        is not set (which is the case).  Not sure whether this code is necessary any longer.
//                // [g_karab]
////                if (this.compiler != null && this.compiler.problemReporter.referenceContext == null) {
////                    this.compiler.problemReporter.referenceContext = this.unit;
////                    this.compiler.problemReporter.jmlEscWarning(message, 0, 0);
////                }
//	            EscjavaMarker.report(null,severity,loc,length,message);
//	        } else {
//	            int soffset = 0;
//	            int eoffset = 0;
//	            String msg="";
//	            // The following is the file reported in the error message
//	            // It is a file-system path name in native OS format
//	            String errorFileName = javafe.util.Location.toFileName(loc);
//	            // The following is the file being compiled
//                // FIXME: this.unit is no longer set we may want to eliminate/rethink the next two lines. [g_karab]
//	            String compFileName = null;
//	            if (this.unit != null) new String(this.unit.getFileName());
//	            // Are they the same?
//	            // FIXME - need to test that the following works in situations where the errorFile is only
//	            // linked into the workspace, or there are UNIX style links in the paths
//	            // What about Windows aliases?
//	            IPath p = new Path(errorFileName).makeAbsolute(); // absolute file-system path
//	            IPath pp = compFileName == null ? null : new Path(compFileName); // path relative to the workspace root
//	            // FIXME - the following two lines are subject to NPEs in unusual/corrupt situations
//	            if (pp != null) pp = ResourcesPlugin.getWorkspace().getRoot().findMember(pp).getLocation();
//	            boolean sameFile = pp == null || p.equals(pp);
//	            if (!sameFile) {
//	                // Put filename in message, if it is a different file
//	                msg = javafe.util.Location.toFileName(loc) + ":";
//	            }
//	            if (!javafe.util.Location.isWholeFileLoc(loc)) {
//	                if (sameFile) {
//	                    // If length is negative, it means we do not know the length of the relevant section
//	                    // of code to highlight.  So just do one character.
//	                    soffset = javafe.util.Location.toOffset(loc);
//	                    eoffset = soffset + (length<0? 1: length);
//	                    // FIXME - ideally if the error is reported for a different file than the one we
//	                    // are processing we would put a marker on that other file.  For now we are not doing
//	                    // that and are just reporting a non-line specific error marker for the compilation unit.
//	                    // Hence we calculate the offsets only if the error is line-specific AND the files are the
//	                    // same.
//	                }
//	                // Put line number in message if the location is line-specific
//	                msg = msg + javafe.util.Location.toLineNumber(loc) + ":";
//	            }
//	            msg = msg + message;
//                EscjavaMarker.report(p,severity,loc,length,message); // TODO - or msg.  If message, do not have to do some of the stuff above
//                // FIXME: this.unit is no longer set we may want to eliminate/rethink the next two lines. [g_karab] 
//	            if (this.compiler != null && this.compiler.problemReporter.referenceContext == null )
//	                this.compiler.problemReporter.referenceContext = this.unit;
//	            // FIXME: distinguish between warnings, errors, cautions,
//	            // etc.
//
//	    	}
//	    }
//
//        public void reportAssociatedInfo(int loc) {
//            if (loc == Location.NULL) return;
//
//            String filename = null;
//            int line = 0;
//            int cpos = 0;
////            if (Location.isWholeFileLoc(loc)) {
////                GenericFile f = Location.toFile(loc);
////                filename = f.getHumanName();
////                if (f instanceof java.io.File) {
////                    filename = ((java.io.File)f).getAbsolutePath();
////                }
////            } else {
////                GenericFile f = Location.toFile(loc);
////                filename = f.getHumanName();
////                if (f instanceof java.io.File) {
////                    filename = ((java.io.File)f).getAbsolutePath();
////                }
////                line = Location.toLineNumber(loc);
////                cpos = Location.toOffset(loc);
////            }
//
//            IResource res = null;
//            if (filename != null) {
//                
//                // FIXME - this works as long as the filename coming in
//                // is a totally absolute file-system path name
//                // Is it ever something else?  Can we tell and adjust using 
//                // java system calls?
//                // DOes it work when the file is linked? - e.g. specs files
//                IPath filePath = new Path(filename);
//                IFile ffile = /*UIUtils.*/getRoot().getFileForLocation(filePath);
//                res = ffile;
//                // TODO
////              if (res == null) {
////                  // It is likely that filePath is an absolute path to
////                  // a linked resource
////                  IResource s = Utils.mapBack(JavaCore.create(resource.getProject()),file,false);
////                  res = s != null ? s : resource;
////              }
//            }
//            
//            if (Log.on) {
//                Log.log("ASSOCIATED INFO " + filename + " " + line + " " + cpos);
//            }
//            
//            try {
//                addMarkerInfo(filename,line,cpos);
//            } catch (CoreException e) {
//                Log.errorlog("Failed to associated info", e);
//            }
//        }
//
////        public void reportAssociatedInfo2(int loc, ClipPolicy cp) {
////            reportAssociatedInfo(loc);
////        }
//
//
//	}

    /**
     * @return The singleton IWorkspaceRoot for the workspace
     */
    public static IWorkspaceRoot getRoot() {
        return ResourcesPlugin.getWorkspace().getRoot();
    }
	
}

// FIXME - escjava problem markers are off by default?
// FIXME - escjava checking is off by default?
// FIXME - need to appropriately show associated information
// FIXME - get options in preferences
// FIXME - get spec path correct (seems to read built-in specs)
// FIXME - get accelerator keys to work
// FIXME - cleaning should delete all markers
// FIXME - duplicate markers are produced!!!!

// FIXME - clean up positioning of marker

// FIXME - if there is concurrency then the caching of project for jmlFailed is bad

/* Eclipse problem?  When a property page is first brought up
 * by selecting a proejct and Alt-Enter, then when asking for
 * the escjava properties, a warning message comes up. Thereafter
 * things seem to work ok.
 */
