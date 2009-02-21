/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Jul 30, 2004
 */
package org.jmlspecs.eclipse.jdt.ui;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.util.SafeRunnable;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.IProgressService;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;
import org.jmlspecs.eclipse.jdt.internal.esc2.EscJava2Wrapper;

/**
 * This class and its subclasses are the classes
 * that respond to Menu actions.
 * 
 * @author David R. Cok
 *
 */
public abstract class EscjavaAction implements IObjectActionDelegate,
										IWorkbenchWindowActionDelegate {

	/** Caches the value of the window, when informed of it. */
	protected IWorkbenchWindow window;
	
	/** Caches the value of the shell in which the window exists. */
	protected Shell shell = null;
	
	/** The current selection. */
	protected ISelection selection;
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(org.eclipse.jface.action.IAction, org.eclipse.ui.IWorkbenchPart)
	 */
	public final void setActivePart(final IAction action, final IWorkbenchPart targetPart) {
	  //System.out.println("SET ACTIVE PART");
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
	 */
	public final void selectionChanged(final IAction action, final ISelection selection) {
		this.selection = selection;
		//System.out.println("SEL CHANGED " + selection.getClass());
	}

	/**
	 * We can use this method to dispose of any system
	 * resources we previously allocated.
	 * @see IWorkbenchWindowActionDelegate#dispose
	 */
	public void dispose() {
	}
	
	/**
	 * We will cache window object in order to
	 * be able to provide parent shell for the message dialog.
	 * @param window The parent window
	 * @see IWorkbenchWindowActionDelegate#init
	 */
	public void init(IWorkbenchWindow window) {
		this.window = window;
		this.shell = window.getShell();
	}

	/**
	 * Shows a message to the user; call this only for situations 
	 * in which we are already running in the UI thread.
	 * @param msg  The message to show
	 */
	protected void showMessage(String msg) {
		UIUtils.showMessageInUI(window.getShell(),"ESC/Java2 Operation",msg);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
	public void run(final IAction action) {
		// Called in response to a menu selection (or other command)
		// Either this or some of the component template routines
		// (iterator, start, doit, end) should be overridden for
		// individual menu items
		try {
			//if (useProjects()) {
		  if (true) {
				Map map = UIUtils.sortByProject(UIUtils.getSelectedElements(selection,window));
				iterateByProject(map);
			} else {
				Map map = UIUtils.sortByPackageFragmentRoot(UIUtils.getSelectedElements(selection,window));
				iterateByPFR(map);			
			}
//		} catch (JMLEclipseCancel e) {
//			throw e;  // FIXME - where does this get caught?
		} catch (Exception e) {
			Log.errorlog("Exception occurred in executing a menu item action: ",e);
		}
	}

	/**
	 * Iterates over all the projects in the map (as produced by
	 * getJavaElements()), calling start/doit/end for each project's collection
	 * of IJavaElements and IResources.  The order of iteration is that supplied by
	 * orderedProjectsIterator(map).  The map must be indexed by project.
	 * 
	 * Expected to be called in the UI thread.
	 * @param map The map containing IJavaProjects and their Collections of
	 * IJavaElements and IResources.
	 */
	public void iterateByProject(Map map) {
		boolean nothing = true;
		Iterator ii = orderedProjectIterator(map.keySet());
		while (ii.hasNext()) {
			IJavaProject jp = JavaCore.create((IProject)ii.next());
			Collection elements = (Collection)map.get(jp);
			if (Log.on) Log.log("  Doing project " + jp.getElementName() + " " + elements.size() + " items");
			if (!elements.isEmpty()) nothing = false;
			// Catch exceptions here so that we can continue on after an error
			// in one project to do other projects
			try {
				if (!start(jp,elements)) continue;
				Iterator iii = elements.iterator();
				while (iii.hasNext()) {
					Object o = iii.next();
					boolean ok = doit(o);
					if (!ok) {
						if (Log.on) Log.log("Unable to process an item of type " + o.getClass());
						showMessage("Unable to process an item of type " + o.getClass());
					}
				}
				end(jp,elements);
//			} catch (JMLEclipseCancel e) {
//				throw e;
			} catch (Exception e) {
				Log.errorlog("Exception occurred while processing project " + jp.getElementName(),e);
				showMessage("Exception in project " + jp.getElementName() + ": " + e.toString());
			}
		}
		if (nothing) {
			if (Log.on) Log.log("No relevant objects");
			showMessage("No relevant objects");
		}

	}

	/**
	 * Iterates over all the package fragment roots in the map,
	 * calling start/doit/end for each package fragment root and
	 * its Collection.  The map must be indexed by package fragment root.
	 * @param map The map containing IPackageFragmentRoot keys and Collection values
	 */
	public void iterateByPFR(Map map) {
		Iterator ii = map.keySet().iterator();
		boolean nothing = true;
		while (ii.hasNext()) {
			IPackageFragmentRoot pfr = (IPackageFragmentRoot)ii.next();
			Collection elements = (Collection)map.get(pfr);
			if (!elements.isEmpty()) nothing = false;
			// Catch exceptions here so that we can continue on
			// with other items to be done
			try {
				if (!start(pfr,elements)) continue;
				Iterator i = elements.iterator();
				while (i.hasNext()) {
					Object o = i.next();
					boolean ok = doit(o);
					if (!ok) {
						showMessage("Unable to process an item of type " + o.getClass());
					}
				}
				end(pfr.getJavaProject(),elements);
//			} catch (JMLEclipseCancel e) {
//				throw e;
			} catch (Exception e) {
				showMessage("Exception while acting on folder " + pfr.getElementName() + ": " + e.getMessage());
				Log.errorlog("Exception while acting on folder " + pfr.getElementName(),e);
			}
		}
		if (nothing) {
			showMessage("No relevant objects");
		}

	}

	/**
	 * Sorts the projects in the map into an order such that any project
	 * follows all of those it requires (that are in the map).
	 * 
	 * @param map A map whose keys are IProject objects.
	 * @return An array of the keys of the map (which are IProject
	 * 		objects) sorted so that any project comes after projects
	 * 		that it requires.
	 */
	protected IProject[] orderedProjects(Collection c) {
		IProject projects[] = new IProject[c.size()];
		Iterator i = c.iterator(); int j = 0;
		while (i.hasNext()) { projects[j++] = ((IJavaProject)i.next()).getProject(); }
		return ResourcesPlugin.getWorkspace().computeProjectOrder(projects).projects;
	}	
	
	/**
	 * Returns an iterator over the project array returned by orderedProjects()
	 * 
	 * @param map
	 * @return An Iterator that iterates over the keys of the map 
	 * 		(which are IProject objects) in order, with projects
	 * 		required coming before those that require them.
	 */
	protected Iterator orderedProjectIterator(Collection c) {
		return Arrays.asList(orderedProjects(c)).iterator();
	}
	
	/**
	 * Called prior to processing the Collection of elements for the
	 * given project.  If false is returned, this will be the end of 
	 * processing for this project; if true is returned, then doit is 
	 * called on each element of the Collection followed by calling end.
	 * @param jp  The IJavaProject whose elements are being processed
	 * @param elements The filenames of files to be processed
	 * @return Return true if processing is to continue with each element; false if this method contains all the processing to be performed
	 * @throws Exception
	 */
	protected boolean start(IJavaProject jp, Collection elements) throws Exception { return true; }

	/**
	 * Called prior to processing the Collection of elements for the
	 * given package-fragment-root.  If false is returned, this will be the end of 
	 * processing for this package-fragment-root; if true is returned, then doit is 
	 * called on each element of the Collection followed by calling end.
	 * @param pfr  The IPackageFragmentRoot whose elements are being processed
	 * @param elements The filenames of files to be processed
	 * @return Return true if processing is to continue with each element; false if this method contains all the processing to be performed
	 * @throws Exception
	 */
	protected boolean start(IPackageFragmentRoot pfr, Collection elements) throws Exception { return true; }
	

	/**
	 * Called after each element of a given project has been processed (via doit)
	 * @param jp  The project whose elements are being processed
	 * @param elements  The filenames of the files/folders being processed
	 * @return Ignored // FIXME
	 * @throws Exception
	 */
	protected boolean end(IJavaProject jp, Collection elements) throws Exception { return true; }
	
	/**
	 * Executes the processing for one element (the argument).
	 * @param o The object to be processed
	 * @return true if the object was processed successfully, false otherwise.
	 * @throws Exception
	 */
	protected boolean doit(Object o)
					throws Exception { return true; }
	
//	/**
//	 * Calls doit for each java project within the workspace;
//	 * continues on even if one project fails.
//	 * 
//	 * @return false if any one project fails, true if all succeed
//	 * @throws Exception
//	 */
//	protected boolean doWorkspace() throws Exception {
//		boolean b = true;
//		IJavaProject[] projects = UIUtils.getJavaProjects();
//		for (int i = 0; i<projects.length; ++i) {
//			boolean bb = doit(projects[i]);
//			if (!bb) b = false;
//		}
//		return b;
//	}
	/**
	 * This calls doit on every (non-archive) package fragment within the project.
	 * 
	 * @param p - the project whose packages are to be operated on
	 * @return false if any one item fails, true if all succeed
	 * @throws Exception
	 */
	protected boolean doProject(IJavaProject p) throws Exception {
		org.eclipse.jdt.core.IPackageFragmentRoot[] pr = p.getPackageFragmentRoots();
		boolean b = true;
		for (int kk=0; kk<pr.length; ++kk) {
			if (pr[kk].isArchive()) continue;
			doPackageFragmentRoot(pr[kk]);
		}
		return b;
	}

	/**
	 * This calls doit on every package within the package fragment root.
	 * 
	 * @param p - the package fragment whose compilation units are to be operated on
	 * @return false if any one item fails, true if all succeed
	 * @throws Exception
	 */
	protected boolean doPackageFragmentRoot(IPackageFragmentRoot p) throws Exception {
		IJavaElement[] pfs = p.getChildren();
		boolean b = true;
		for (int i = 0; i<pfs.length; ++i) {
			IPackageFragment pf = (IPackageFragment)pfs[i];
			boolean bb = doPackageFragment(pf);
			if (!bb) b = false;
		}
		return b;
	}
	
	/**
	 * This calls doit on every compilation unit within the package fragment.
	 * 
	 * @param p - the package fragment whose compilation units are to be operated on
	 * @return false if any one item fails, true if all succeed
	 * @throws Exception
	 */
	protected boolean doPackageFragment(IPackageFragment p) throws Exception {
		ICompilationUnit[] cus = p.getCompilationUnits();
		boolean b = true;
		for (int j=0; j<cus.length; ++j) {
			ICompilationUnit cu = cus[j];
			boolean bb = doit(cu);
			if (!bb) b = false;
		}
		return b;
	}

	/**
	 * This class implements the action for checking
	 * files using EscJava2
	 * 
	 * @author David R. Cok
	 */
	public static class Check extends EscjavaAction {
		public final void run(final IAction action) {
			try {
				Iterator i = UIUtils.getSelectedElements(selection,window).iterator();
				if (!i.hasNext()) {
					UIUtils.showMessageInUI(
							shell,
							"ESCJava Plugin",
							"Nothing to check");
				}
				
				// First clear the markers and touch all the elements
				final Set projects = new HashSet();
				while (i.hasNext()) {
				    Object o = i.next();
				    boolean checked = false;
				    if (o instanceof IJavaElement) {
				        IJavaElement e = (IJavaElement)o;
				        checked = touchJavaElement(e);
				        projects.add(e.getJavaProject());
				    } else if (o instanceof IResource) {
				        // If an item is selected that is not a Java resource or
				        // if it is selected within a Navigator view, then we
				        // receive a generic IResource rather than a Java Element
				        // So we try to see if it can be converted
				        IResource p = (IResource)o;
				        IProjectNature n = p.getProject().getNature(JavaCore.NATURE_ID);
				        if (n != null) {
				            IJavaElement jp = JavaCore.create(p);
				            checked = touchJavaElement(jp);
	                        projects.add(jp.getJavaProject());
				        }
				    }
					if (!checked) {
						String msg = "Cannot check " + o.getClass();
						UIUtils.showMessageInUI(
									shell,
									"ESCJava Plugin",
									msg);
					}
					
				}
				
                // NOTE: We are invoking the whole JDT compilation mechanism rather
                // than calling ESC directly because eventually we will integrate
                // ESC into the JDT and then we will have to use the JDT to produce
                // the ASTs needed by ESC.  In order to make the JDT compiler 
                // recompile, the file has to be touched; this has the side-effect
                // of an unnecessary recompile happening as well.  This can't be
                // avoided without having different kinds of dirtiness caused by
                // touching.
				
				// TODO - However, if the ASTs exist beyond a compilation and can
				// be retrieved on demand, we could re-implement this to act on
				// the ASTs directly, once that connection is made to ESC.

				// Now do the build - since the build is done by project, we do
				// it at the end so we can do it once for each project represented
				// by all of the selected items.
				
                // FIXME - multi-thread this? should we fork and keep the UI going?
				// FIXME - implement cancellation - does cancelling in the middle of a big project actually work?
				// FIXME - this operates on the saved file; the results can be
				// misleading if the file has not been saved - perhaps a warning?

				EscJava2Wrapper.manualRun = true;
				try {
				    IProgressService progress = PlatformUI.getWorkbench().getProgressService();

				    IRunnableWithProgress job = new IRunnableWithProgress() {
				        public void run(IProgressMonitor monitor) {
				            monitor.setTaskName("Static checking");
				            Iterator i = orderedProjectIterator(projects);
				            while (i.hasNext()) {
				                try {
				                    IProject project = (IProject)i.next();
				                    project.build(IncrementalProjectBuilder.INCREMENTAL_BUILD, monitor);
				                } catch (Exception e) {
				                    Log.errorlog("Exception occurred in running ESCJava checks: ",e);
				                }
				            }
				        }
				    };
				    progress.run(false,true,job);
				} finally {
				    EscJava2Wrapper.manualRun = false;
				}


			} catch (Exception e) {
				if (window != null) {
					UIUtils.showMessageInUI(
							shell,
							"ESCJava Plugin - exception",
							e.toString());
				}			
			}
		}
		
		// FIXME - would like to be able to run ESC on a method or type as well
		

		/**TODO
		 * @param element
		 * @return
		 * @throws Exception
		 */
		public boolean touchJavaElement(IJavaElement element) 
		throws Exception {
		    if (element instanceof IJavaProject) {
		        IJavaProject javaProject = (IJavaProject)element;
	            IPackageFragment[] packages = javaProject.getPackageFragments();
	            for (int i = 0; i<packages.length; ++i) {
	                IPackageFragment p = packages[i];
	                ICompilationUnit[] cus = p.getCompilationUnits();
	                for (int j=0; j<cus.length; ++j) {
	                    ICompilationUnit cu = cus[j];
	                    cu.getResource().touch(null);
	                }
	            }
	            EscjavaMarker.clearMarkers(javaProject.getProject());
		    } else if (element instanceof IPackageFragment) {
		        IPackageFragment p = (IPackageFragment)element;
	            ICompilationUnit[] cus = p.getCompilationUnits();
	            for (int j=0; j<cus.length; ++j) {
	                ICompilationUnit cu = cus[j];
	                cu.getResource().touch(null); // See checkProject about touching
	            }
	            EscjavaMarker.clearMarkers(p.getResource());
		    } else if (element instanceof ICompilationUnit) {
		        ICompilationUnit p = (ICompilationUnit)element;
	            IResource resource = p.getUnderlyingResource();
	            resource.touch(null); // See checkProject about touching
	            ArrayList list = new ArrayList(1);
	            list.add(resource.getLocation().toOSString());
	            EscjavaMarker.clearMarkers(resource);
		    } else if (element instanceof IType) {
                System.out.println("CHECK TYPE");
//		        checkType((IType)element);
		    } else {
	              System.out.println("CHECK OTHER");
		        return false;
		    }
		    return true;
		}
		
	}

	/**
	 * This class implements the action that clears
	 * EscJava markers.
	 * 
	 * @author David R. Cok
	 */
	public static class Clear extends EscjavaAction {
		public final void run(final IAction action) {
            Iterator i = UIUtils.getSelectedElements(selection,window).iterator();
            while (i.hasNext()) {
                Object o = i.next();
                // FIXME - combine the errors into one error dialog?
                try {
                    if (o instanceof IResource) {
                        EscjavaMarker.clearMarkers((IResource)o);
                    } else if (o instanceof IJavaElement) {
                        IResource r = ((IJavaElement)o).getCorrespondingResource();
                        // FIXME - check the behavior of the following if the IJavaElement is smaller than a ocmpilation unit
                        if (r != null) EscjavaMarker.clearMarkers(r);
                    }
                } catch (Exception e) {
                    if (window != null) {
                        MessageDialog.openInformation(
                                window.getShell(),
                                "Escjava Plugin - exception",
                                e.toString());
                    }			
                }
            }
			return;
			
		}
	}

	/**
	 * This class implements the action that opens and
	 * positions an editor on an associated declaration of
	 * a marker.
	 * 
	 * @author David R. Cok
	 */
	public static class GoToDecl extends EscjavaAction {
		public final void run(final IAction action) {
		  //System.out.println("ACTION " + action.getClass());
			WarningDeclarationsAction.run(shell,window,selection);
		}
	}

//	/**
//	 * This action enables the JML nature on the selected projects.
//	 * 
//	 * @author David Cok
//	 *
//	 */
//	static public class EnableEscjava extends EscjavaAction {
//		// This is all done in the UI thread with no progress
//		// FIXME - is it fast enough?
//		
//		public final void run(final IAction action) {
//			try {
//				Map map = Utils.sortByProject(Utils.getSelectedElements(selection,window));
//				Iterator i = map.keySet().iterator();
//				while (i.hasNext()) {
//					IProject p = ((IJavaProject)i.next()).getProject();
//					EscjavaPlugin.getPlugin().addEscjavaAutocheckNature(p);
//				}
//				// Update the decorators in the UI thread
//				Display.getDefault().syncExec(new java.lang.Runnable() {
//				  public void run() {
//				    PlatformUI.getWorkbench().getDecoratorManager().update(
//				        EscjavaPlugin.PLUGINID + ".ESCDecoratorA");
//				  }
//				});
//			} catch (Exception e) {
//				Log.errorlog("Failed to enable Esc/Java nature", e);
//			}
//			if (Log.on) Log.log("Completed Enable Esc/Java operation " + (new Date()));
//		}
//	}

//	/**
//	 * @author David Cok
//	 *
//	 * Implements an action that lists selected files as
//	 * enabled for RAC.
//	 */
//	static public class EnableESC extends ESC {
//		public void action(IResource resource) { 
//		  AutoCheckBuilder.add(resource); 
//		}
//
//		public void run(final IAction action) {
//			super.run(action);
//			if (Log.on) Log.log("Completed Enable Esc/Java action " + (new Date().toString()));
//		}
//}

//	/**
//	 * @author David Cok
//	 *
//	 * Implements an action that removes selected files from
//	 * the RAC enabled list.
//	 */
//	static public class DisableESC extends ESC {
//		public void action(IResource resource) { AutoCheckBuilder.remove(resource); }
//
//		public void run(final IAction action) {
//			super.run(action);
//			if (Log.on) Log.log("Completed Disable Esc/Java action " + (new Date().toString()));
//		}
//	}

//	/**
//	 * This action disables the JML nature on the selected projects.
//	 * 
//	 * @author David Cok
//	 *
//	 */
//	static public class DisableEscjava extends EscjavaAction {
//		// This is all done in the UI thread with no progress
//		// FIXME - is it fast enough?
//
//		public final void run(final IAction action) {
//			try {
//				Map map = Utils.sortByProject(Utils.getSelectedElements(selection,window));
//				Iterator i = map.keySet().iterator();
//				while (i.hasNext()) {
//					IProject p = ((IJavaProject)i.next()).getProject();
//					EscjavaPlugin.getPlugin().removeEscjavaAutocheckNature(p);
//				}
//				// Update the decorators in the UI thread
//				Display.getDefault().syncExec(new java.lang.Runnable() {
//				  public void run() {
//				    PlatformUI.getWorkbench().getDecoratorManager().update(
//				        EscjavaPlugin.PLUGINID + ".ESCDecoratorA");
//				  }
//				});
//			} catch (Exception e) {
//				Log.errorlog("Failed to disable Esc/Java nature",e);
//			}
//			if (Log.on) Log.log("Completed Disable Esc/Java operation " + (new Date()));
//		}
//	}

	/**
	 * @author David Cok
	 *
	 * A base class for the enable and disable RAC classes.
	 */
	static abstract public class ESC extends EscjavaAction {
		// FIXME - this all happens in the UI thread with no progress - is that ok?
		//  the touch operation could use a monitor
		// These operations just read information from the UI
		// and resources and change the Escjava.enabled collection.
		
		/** A collection of IResource objects that need to
		 *  be recompiled.
		 */
		private Collection touch;

		
		protected boolean start(IJavaProject jp, Collection c) {
			touch = new LinkedList();
			return true;
		}

		protected boolean doit(Object o) throws Exception {
			boolean b;
			if (o instanceof ICompilationUnit) {
				ICompilationUnit p = (ICompilationUnit)o;
				IResource resource = p.getCorrespondingResource();
				if (resource == null) return false;
				action(resource);
				
				// Need to touch the file in order to force
				// recompilation
				touch.add(resource);
				b = true;
			} else if (o instanceof IFile) {
				action((IFile)o);
				touch.add(o);
				b = true;
				// FIXME - should we do IFolder?
			} else if (o instanceof IJavaProject) {
				b = doProject((IJavaProject)o);
			} else if (o instanceof IPackageFragmentRoot) {
				b = doPackageFragmentRoot((IPackageFragmentRoot)o);
			} else if (o instanceof IPackageFragment) {
				b = doPackageFragment((IPackageFragment)o);
			} else if (o instanceof IWorkspace) {
				b = false; // TODO doWorkspace();
			} else {
				b = false;
			}
			return b;
		}
		
		/**
		 * The base class has common behavior for everthing but
		 * the action to be performed on each resource; this method
		 * is overridden to do the appropriate action.
		 * 
		 * @param r  The resource to be acted upon.
		 */
		abstract protected void action(IResource r);
		
		protected boolean end(IJavaProject jp, Collection elements) {
			final Collection touchList = touch;
			// FIXME - is this the right thread to use
			SafeRunner.run(new SafeRunnable() {
				public void run() throws Exception {
					Iterator i = touchList.iterator();
					while (i.hasNext()) {
						IResource r = (IResource)i.next();
						r.touch(null);
					}
				}
			});
			// Update the decorators in the UI thread
			Display.getDefault().syncExec(new java.lang.Runnable() {
        public void run() {
          PlatformUI.getWorkbench().getDecoratorManager().update(
              Activator.PLUGIN_ID + ".ESCDecorator");
        }
      });
			touch = null;
			// FIXME - touch needs to be set null no matter
			// what exceptions happen where in start/doit/end
			return true;
		}
	}

}
// FIXME -need javadoc comments
	
