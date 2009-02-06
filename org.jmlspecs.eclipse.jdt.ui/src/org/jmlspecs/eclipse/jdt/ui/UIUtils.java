/*
 * This file is part of a library of utilities for plugin projects.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 6, 2004
 */
package org.jmlspecs.eclipse.jdt.ui;

import java.io.BufferedInputStream;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;
import org.osgi.framework.Bundle;

/**
 * This class contains a number of (static) utility methods for
 * use in plugins.
 * 
 * @author David R. Cok
 */
public class UIUtils {

	/** A convenience holder for the end-of-line String for the current platform. */
	final static public String eol = System.getProperty("line.separator"); // FIXME - is this right?

    /**
     * @return The singleton IWorkspaceRoot for the workspace
     */
    public static IWorkspaceRoot getRoot() {
        return ResourcesPlugin.getWorkspace().getRoot();
    }
    
	/**
	 * Displays a message in a dialog in the UI thread - this may
	 * be called from other threads.
	 * @param sh  The shell to use to display the dialog, or 
	 * 		a top-level shell if the parameter is null
	 * @param title  The title of the dialog window
	 * @param msg  The message to display in the dialog
	 */
	//@ requires title != null;
	//@ requires msg != null;
	static public void showMessageInUI(Shell sh, final String title, final String msg) {
		final Shell shell = sh;
		Display d = shell == null ? Display.getDefault() : shell.getDisplay();
		d.asyncExec(new Runnable() {
				public void run() {
					MessageDialog.openInformation(
							shell,
							title,
							msg);
				}
			});
	}

	/**
	 * Displays a message in a information dialog; must be called from the UI thread.
	 * @param shell  Either the parent shell, or null for a top-level shell
	 * @param title  A title for the dialog window
	 * @param msg   The message to display in the dialog window
	 */
	//@ requires shell != null;
	//@ requires title != null;
	//@ requires msg != null;
	static public void showMessage(Shell shell, String title, String msg) {
			MessageDialog.openInformation(
				shell,
				title,
				msg);
	}

	
	/**
	 * This method interprets the selection returning a List
	 * of IJavaElement and IResource objects that the plugin
	 * knows how to handle.
	 * 
	 * @param selection  The selection to inspect
	 * @param window  The window in which a selected editor exists
	 * @return A List of IJavaElement and IResource
	 */
	public static List getSelectedElements(ISelection selection, IWorkbenchWindow window ) {
		List list = new LinkedList();
		if (!selection.isEmpty()) {
			if (selection instanceof IStructuredSelection) {
				IStructuredSelection structuredSelection = (IStructuredSelection) selection;
				for (Iterator iter = structuredSelection.iterator(); iter.hasNext(); ) {
					Object element = iter.next();
					if (element instanceof IJavaElement) {
						list.add(element);
					} else if (element instanceof IResource) {
						list.add(element);
					}
				}
			} else if (selection instanceof ITextSelection){
				IEditorPart editor = window.getActivePage().getActiveEditor();
				IResource resource = (IResource) editor.getEditorInput().getAdapter(IFile.class);
				IJavaElement element = JavaCore.create(resource);
				if (element != null)
					list.add(element);
				else
					list.add(resource);
			}
		}
		return list;
	}

    /**
     * A convenience method for getting all of the Java projects in the 
     * workspace.
     * @return An array of the IJavaProject objects in the workspace
     */
    public static IJavaProject[] getJavaProjects() {
        IProject[] projects = getRoot().getProjects();
        Collection list = new LinkedList();
        for (int i=0; i<projects.length; ++i) {
            IJavaProject jp = JavaCore.create(projects[i]);
            if (jp != null) list.add(jp);
        }
        return (IJavaProject[]) list.toArray(new IJavaProject[list.size()]);
    }

    
    /**
     * Computes the classpath (in terms of full absolute file-system paths to
     * directories) from the information available in the Eclipse project.
     * Note that this involves recursively processing the classpath contributions
     * from projects that are on the Eclipse classpath for the requested project.
     *
     * @param project The project whose classpath is to be determined.
     * @return The classpath of the argument in full absolute file-system paths,
     *      separated by the platform's path separator
     */
    // FIXME - may need to distinguish source and binary classpaths?
    static public String getProjectClassPath(IJavaProject project) {

        StringBuffer classPath = new StringBuffer(System.getProperty("java.class.path"));
        List list = new LinkedList();

        addResolvedClassPathEntries(list,project,false);

        Iterator i = list.iterator();
        while (i.hasNext()) {
            classPath.append(java.io.File.pathSeparator);
            classPath.append(i.next());
        }
        return classPath.toString();
    }
    
    /**
     * Gets the classpath entries for the given project and adds
     * them to the List as file-system absolute paths (String);
     * required projects are added recursively; libraries are added
     * once; source folders are converted to file system absolute
     * paths (remember that source folders may be linked).
     * 
     * @param project
     * @return List of String containing classpath locations
     */
    static public List getProjectClassPathEntries(IJavaProject project) {
        //StringBuffer classPath = new StringBuffer(System.getProperty("java.class.path"));
        List list = new LinkedList();       
        addResolvedClassPathEntries(list,project,false);
        return list;
        // FIXME - does not include the system entries
    }

    /** TODO
     * @param list
     * @param project
     * @param onlyExported
     */
    // FIXME - Ought to use the information that a classpathentry is exported, but the
    // value of cpe.isExported() does not seem to reflect the setting in the Java BuildPath properties.
    // Thus here we arbitrarily state that only source entries are exported, not
    // libraries or projects.
    static void addResolvedClassPathEntries(List list, IJavaProject project, boolean onlyExported) {
        try {
            IClasspathEntry[] classPathEntries = project.getResolvedClasspath(false);

            for (int i = 0; i < classPathEntries.length; ++i) {
                IClasspathEntry cpe = classPathEntries[i];
                IPath entry = cpe.getPath();
                if (onlyExported && 
                        (cpe.getEntryKind() != IClasspathEntry.CPE_SOURCE &&
                                !entry.toOSString().endsWith("jmlspecs.jar") )) continue; // FIXME no explicit library names
                IResource res = getRoot().findMember(entry);
                if (cpe.getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
                    // Might be an internal or external library
                    if (res != null) {
                        // internal
                        list.add(res.getRawLocation().toOSString());
                        // NOTE: Per the note below, it is not entirely clear
                        // whether the above should be getLocation or getRawLocation
                        // FIXME - try a linked library, if that is possible
                    } else {
                        // external
                        list.add(entry.toOSString());
                    }
                } else if (cpe.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
                    // The Eclipse documentation is a bit unclear or at odds with
                    // the actual behavior.  What I observe is that
                    // - a linked folder gives the same result for getLocation and getRawLocation
                    // - a project that is also a source folder gives null for getRawLocation
                    // Thus experiment would indicate that getLocation could always be used,
                    // but the documentation implies one could always use getRawLocation.  The following
                    // code is trying to be conservative. (NOTE)
                    if (res.isLinked()) list.add(res.getRawLocation().toOSString());
                    else list.add(res.getLocation().toOSString());
                } else if (cpe.getEntryKind() == IClasspathEntry.CPE_PROJECT) {
                    IJavaProject jp = JavaCore.create((IProject)res);
                    if (jp != null) addResolvedClassPathEntries(list,jp,true);
                    else {
                        // FIXME - throw an error of some sort
                    }
                } else {
//                  Log.errorlog("Unexpected content kind as a classpath entry: " + cpe.getEntryKind(),null);
                }
            }
        } catch (JavaModelException e) {
//          Log.errorlog("Unexpected failure to process the classpath: ",e);
        }       
    }
    
    /**
     * Creates a map indexed by IJavaProject, with the value for
     * each IJavaProject being a Collection consisting of the subset
     * of the argument that belongs to the Java project.
     * 
     * @param elements The set of elements to sort
     * @return The resulting Map of IJavaProject to Collection
     */
    /*@ requires elements != null;
     requires elements.elementType <: IResource ||
              elements.elementType <: IJavaElement;
     ensures \result != null;
     */
    public static Map sortByProject(Collection elements) {
        Map map = new HashMap();
        Iterator i = elements.iterator();
        while (i.hasNext()) {
            Object o = i.next();
            IJavaProject jp;
            if (o instanceof IResource) {
                jp = JavaCore.create(((IResource)o).getProject());
            } else if (o instanceof IJavaElement) {
                jp = ((IJavaElement)o).getJavaProject();
            } else {
//              Log.errorlog("INTERNAL ERROR: Unexpected content for a selection List - " + o.getClass(),null);
                continue;
            }
            addToMap(map,jp,o);
        }
        return map;
    }

   /**
    * Creates a map indexed by IPackageFragmentRoot, with the value for
    * each IPackageFragmentRoot being a Collection consisting of the subset
    * of the argument that belongs to the IPackageFragmentRoot.
    * 
    * @param elements The set of elements to sort
    * @return The resulting Map of IJavaProject to Collection
    * @throws CoreException
    */
   /*@ requires elements != null;
       requires elements.elementType <: IResource ||
                elements.elementType <: IJavaElement;
       ensures \result != null;
    */
    public static Map sortByPackageFragmentRoot(Collection elements) throws CoreException {
        Map map = new HashMap();
        Iterator i = elements.iterator();
        while (i.hasNext()) {
            Object o = i.next();
            IPackageFragmentRoot pfr = null;
            if (o instanceof IResource) {
                IJavaElement oo = JavaCore.create((IResource)o);
                if (oo != null) o = oo;
                else if (o instanceof IFile) {
                    // Could be a specification file
                    // Find the package fragment root it is in
                    IFile f = (IFile)o;
                    IJavaProject p = JavaCore.create(f.getProject());
                    if (p == null) continue; // everything should be in a Java Project // FIXME - log an error
                    IPackageFragmentRoot[] roots = p.getPackageFragmentRoots();
                    IPath path = f.getFullPath();
                    for (int k=0; k<roots.length; ++k) {
                        IPackageFragmentRoot root = roots[k];
                        IFolder rootFolder = (IFolder)root.getCorrespondingResource();
                        // Is f in (or equal to) rootFolder?
                        if (rootFolder.getFullPath().isPrefixOf(path)) {
                            // rootFolder contains f
                            pfr = root; // This is the one root that contains f
                            break;
                            // added to map at end of method
                        } 
                    }
                    if (pfr == null) {
                        // FIXME - improve this error message
//                      Log.errorlog("FILE is not in a root folder: " + path,null);
                        for (int k=0; k<roots.length; ++k) {
                            IPackageFragmentRoot root = roots[k];
//                          Log.errorlog("  ROOT " + root.getResource().getFullPath(),null);
                        }
                        continue; // FIXME - file is not in a root folder
                    }

                } else if (o instanceof IFolder) {
                    // Could be a folder within a project, such as a source folder or a folder
                    // that holds only specification files (which won't be recognized as a package)
                    // Want any roots within that folder
                    // FIXME - review and test this
                    IFolder f = (IFolder)o;
                    IJavaProject p = JavaCore.create(f.getProject());
                    if (p == null) continue; // everything should be in a Java Project // FIXME - log an error
                    IPackageFragmentRoot[] roots = p.getPackageFragmentRoots();
                    for (int k=0; k<roots.length; ++k) {
                        IPackageFragmentRoot root = roots[k];
                        if (root.isArchive()) continue;
                        IFolder rootFolder = (IFolder)root.getCorrespondingResource();
                        // Is f in (or equal to) rootFolder?
                        if (rootFolder.getFullPath().isPrefixOf(f.getFullPath())) {
                            // rootFolder contains f
                            pfr = root; // This is the one root that contains f
                            // added to map at end of method
                        } else if (f.getFullPath().isPrefixOf(rootFolder.getFullPath())) {
                            // f contains rootFolder
                            addToMap(map,root,root);
                        }
                    }
                    if (pfr == null) continue;
                }
            } else if (o instanceof IJavaProject) {
                // separate out and include all the roots within the project
                IPackageFragmentRoot[] roots = ((IJavaProject)o).getPackageFragmentRoots();
                for (int j = 0; j<roots.length; j++) {
                    pfr = roots[j];
                    if (!pfr.isArchive()) addToMap(map,pfr,pfr);
                }
                continue;
            } else if (o instanceof IJavaElement) {
                if (o instanceof IPackageFragmentRoot) {
                    pfr = (IPackageFragmentRoot)o;
                } else if (o instanceof IPackageFragment) {
                    pfr = (IPackageFragmentRoot)((IPackageFragment)o).getParent();
                } else if (o instanceof ICompilationUnit) {
                    pfr = (IPackageFragmentRoot)((ICompilationUnit)o).getParent().getParent();
                } else {
                    continue; // Log an internal error ??? FIXME
                }
            } else {
                continue; // log an internal error ??? FIXME
            }
            if (pfr.isArchive()) continue;
            addToMap(map,pfr,o);
        }
        return map;
    }

    /**
     * If key is not a key in the map, it is added, with an empty
     * Collection for its value; then the given object is added
     * to the Collection for that key.
     * @param map A map of key values to Collections
     * @param key A key value to add to the map, if it is not
     *      already present
     * @param object An item to add to the Collection for the given key
     */
    private static void addToMap(Map map, Object key, Object object) {
        Collection list = (Collection)map.get(key);
        if (list == null) map.put(key, list = new LinkedList());
        list.add(object);
    }


}
