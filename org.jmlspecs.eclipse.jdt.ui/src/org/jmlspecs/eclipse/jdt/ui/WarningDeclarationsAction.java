package org.jmlspecs.eclipse.jdt.ui;

/*
 * This file is part of the Esc/Java plugin project. Copyright 2004 David R. Cok
 * 
 * Created on Aug 8, 2004.  Altered a bit for the JML4 project.
 */

import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.texteditor.ITextEditor;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;
import org.jmlspecs.eclipse.jdt.internal.esc2.Utils;


/**
 * This is the class that implements the action method for the
 * 'Go To associated specification' menu item - through the run method.  
 * It needs to identify the marker being selected, then find the 
 * associated information in that marker, and finally open an editor on
 * the correct file and location.
 * 
 * @author David Cok
 * 
 */
// FIXME - if we need the event, we have to implement a different interface
public class WarningDeclarationsAction implements
    org.eclipse.ui.IEditorActionDelegate {

  /** Caches the value of the window, when informed of it. */
  protected IWorkbenchWindow window;

  /** Caches the value of the shell in which the window exists. */
  protected Shell shell = null;

  /*
   * (non-Javadoc)
   * 
   * @see org.eclipse.ui.IEditorActionDelegate#setActiveEditor(org.eclipse.jface.action.IAction,
   *      org.eclipse.ui.IEditorPart)
   */
  public void setActiveEditor(IAction action, IEditorPart targetEditor) {
    //System.out.println("IACTION " + action.getClass() + " " + action);
    if (targetEditor != null && targetEditor.getSite() != null) {
      window = targetEditor.getSite().getWorkbenchWindow();
      shell = window == null ? null : window.getShell();
    }
  }

  /*
   * (non-Javadoc)
   * 
   * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
   */
  // This is what actually gets called
  public void run(IAction action) {
    run(shell, window, selection);
  }

  /**
   * TODO
   * 
   * @param shell
   * @param window
   * @param selection
   */
  static public void run(Shell shell, IWorkbenchWindow window,
      ISelection selection) {
    List list = getMarkers(window,selection);
    if (list.isEmpty()) {
      UIUtils.showMessage(shell, "JML-ESC", "No Markers selected");
    } else if (list.size() > 1) {
      UIUtils.showMessage(shell, "JML-ESC",
          "Multiple markers selected - operation applies only to one marker");
    } else {
      IMarker m = (IMarker)list.get(0);
      String s = null;
      try {
        List mlist = EscjavaMarker.getExtraInfo(m);
        if (mlist.isEmpty()) {
          UIUtils.showMessage(shell, "JML-ESC",
              "No associated declarations");
        } else if (mlist.size() == 1) {
          s = (String)mlist.iterator().next();
          openEditor(window, s);
        } else {
          // Need to put up a choice - FIXME
          Iterator i = mlist.iterator();
          if (i.hasNext()) i.next(); // skip the first one
          while (i.hasNext()) {
            openEditor(window, (String)i.next());
          }
          // Do the first one last so it has focus
          s = (String)mlist.iterator().next();
          openEditor(window, s);
        }
      } catch (Exception e) {
        Log.errorlog("Failed to get associated information from a marker: " + s, e);
        UIUtils.showMessage(shell, "JML-ESC",
            "Failed to get associated information: " + s);
      }
    }
  }

  /**
   * Gets all the markers corresponding to the stated selection
   * 
   * @param selection
   * @return List of IMarker objects in selection
   */
  static public List getMarkers(IWorkbenchWindow window, ISelection selection) {
    List list = new LinkedList();
    if (!selection.isEmpty()) {
      if (selection instanceof IStructuredSelection) {
        IStructuredSelection structuredSelection = (IStructuredSelection)selection;
        for (Iterator iter = structuredSelection.iterator(); iter.hasNext();) {
          Object element = iter.next();
          if (element instanceof IMarker) {
            list.add(element);
          }
        }
      } else if (selection instanceof TextSelection) {
        try {
          IWorkbenchPage page = window.getActivePage();
          IEditorPart editor = page.getActiveEditor();
          IEditorInput input = editor.getEditorInput();
          IResource res = (IResource)input.getAdapter(IResource.class);
          IMarker[] markers = res.findMarkers(EscjavaMarker.ESCJAVA_MARKER_ID,true,IResource.DEPTH_INFINITE);
          TextSelection tsel = (TextSelection)selection;
          for (int i = 0; i<markers.length; ++i) {
            //int charstart = markers[i].getAttribute(IMarker.CHAR_START,-1);
            int line = markers[i].getAttribute(IMarker.LINE_NUMBER,-1);
            int selline = tsel.getStartLine()+1;
            System.out.println("MARKER " + line + " SELECTION " + selline);
            if (line == selline) list.add(markers[i]);
          }
        } catch (Exception e) {
          // Just skip - likely this did not look like
          // a standard editor on a file resource with markers
        }
      } else {
        if (Log.on)
            Log.log("Unsupported selection in getMarkers: "
                + selection.getClass());
      }
    }
    return list;
  }

  /**
   * Utility routine that opens up an editor in the given window 
   * corresponding to the data string.  The expected format of the
   * data is a space separated combination of absolute file-system
   * file name, the 1-based line number, and the 0-based character position
   * within the file.
   * 
   * @param window  the workbench window in which we are working
   * @param data    the file, line number, and character position
   * @throws Exception
   */
  static public void openEditor(IWorkbenchWindow window, String data)
      throws Exception {
      
      // Get the filenanme, line number, character position from the string
    int offset = -1;
    int line = -1;
    int k = data.lastIndexOf(' ');
    if (k != -1) {
      offset = Integer.parseInt(data.substring(k + 1));
      data = data.substring(0,k);
      k = data.lastIndexOf(' ');
      if (k != -1) {
        line = Integer.parseInt(data.substring(k + 1));
        data = data.substring(0,k);
      }
    }
    
    // Open the appropriate editor
    String fname = data;
    IPath p = new Path(fname);
    int jk = fname.indexOf(".jar:");
    IWorkbenchPage page = window.getActivePage();
    if (jk == -1) {
        // Not in a jar file
      IFile[] files = UIUtils.getRoot().findFilesForLocation(p);
      //System.out.println("FOUND " + files.length + " FOR " + p);
      for (int j = 0; j < files.length; ++j) {
        if (line <= 0) {
          IMarker marker = files[j].createMarker(IMarker.TEXT);
          marker.setAttribute(IMarker.CHAR_START, offset);  // Without a reasonable CHAR_END, this by itself makes a confusing UI
          IDE.openEditor(page, marker);
          marker.delete();
        } else {
          IMarker marker = files[j].createMarker(IMarker.TEXT);
          marker.setAttribute(IMarker.LINE_NUMBER, line); // Will select the whole line
          //marker.setAttribute(IMarker.CHAR_START, offset);  // Without a reasonable CHAR_END, this by itself makes a confusing UI
          IDE.openEditor(page, marker);
          marker.delete();
        }
        return;
      }
    } else {
        // In a jar file
      String jarfile = fname.substring(0, jk + 4);
      fname = fname.substring(jk + 5);
      try {
        IStorageEditorInput sei = new ZipEditorInput(jarfile, fname);
        IEditorPart ep = IDE.openEditor(page, sei,
            "org.eclipse.jdt.ui.CompilationUnitEditor");
        // FIXME - should the above choose between a Java editor and a Specs editor?
        if (ep instanceof ITextEditor) {
          ((ITextEditor)ep).selectAndReveal(offset-1,0);
        } else {
            // Ignore?  The editor is open, just not on the correct line
        }
        return;
      } catch (IOException e) {
        // skip;
        // Go on to show the display message below
      }
    }
    // The file is not in the current project
    UIUtils.showMessage(window.getShell(), "Open Spec File",
        "The referenced specification is not present in the current project."
            + Utils.eol
            + (fname.length() < 60 ? fname : (fname.substring(0, 60)
                + Utils.eol + fname.substring(60))) + ", line " + line);

  }

  /*
   * (non-Javadoc)
   * 
   * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction,
   *      org.eclipse.jface.viewers.ISelection)
   */
  public void selectionChanged(IAction action, ISelection selection) {
    this.selection = selection;
  }

  /** Cached value of the current selection */
  private ISelection selection = null;
}
