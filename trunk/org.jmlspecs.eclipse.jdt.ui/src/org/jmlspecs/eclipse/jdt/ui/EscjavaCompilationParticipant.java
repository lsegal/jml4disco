package org.jmlspecs.eclipse.jdt.ui;
//@author David Cok
//@date 15 September 2007
//This class is part of the JML-ESC extensions to JDT with the JML4 architecture

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.compiler.BuildContext;
import org.eclipse.jdt.core.compiler.CompilationParticipant;
import org.eclipse.jdt.core.compiler.ReconcileContext;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;
import org.jmlspecs.eclipse.jdt.internal.esc2.EscJava2Wrapper;

/** This class is intended as an Eclipse CompilationParticipant, but
 * so far it does not work.  There is some problem with loading this
 * class in response to using the plugin extension.
 *
 */
public class EscjavaCompilationParticipant extends CompilationParticipant {

    // NOTE: This class is constructed frequently (e.g. on each compile),
    // so do not put one-time initialization code here.  Prior to the first 
    // time an instance of this class is constructed, the containing plug-in
    // is activated, so the Activator.startup method can hold initialization code.
    public EscjavaCompilationParticipant() {
        //System.out.println("CONSTRUCTING");
    }

    public int aboutToBuild(IJavaProject project) {
        //System.out.println("ABOUT TO BUILD");
        EscJava2Wrapper.currentProject = project;
        return super.aboutToBuild(project);
    }

    public void buildStarting(BuildContext[] files, boolean isBatch) {
        // Note: "batch" does not indicate command-line vs. UI, rather it
        // distinguishes different kinds of builds within the UI.
        //System.out.println("BUILD STARTING isBatch="+isBatch);
        super.buildStarting(files,isBatch);
        // This is called when a build is requested (after "aboutToBuild").
        // Note that when builds happen automatically, without an explicit clean,
        // cleanStarting is not called.
        for (int i=0; i<files.length; i++) {
            try {
                EscjavaMarker.clearMarkers(files[i].getFile());
            } catch (CoreException e) {
                Log.errorlog("Failed to clean markers from file " + files[i].getFile().getName(),e);
            }
        }
    }

    public void cleanStarting(IJavaProject project) {
        //System.out.println("CLEAN STARTING " + project.getElementName());
        super.cleanStarting(project);
        // This is called when a Clean is explicitly requested, without or
        // without a build automatically afterwards.
        try {
            EscjavaMarker.clearMarkers(project.getProject());
        } catch (CoreException e) {
            Log.errorlog("Failed to clean markers from project " + project.getElementName(),e);
        }
    }

    public boolean isActive(IJavaProject project) {
        //System.out.println("ISACTIVE " + project.getElementName());
        return true;
    }

    public boolean isAnnotationProcessor() {
        //System.out.println("ISANNOTATIONPROCESSOR ");
        return super.isAnnotationProcessor();
    }

    public void processAnnotations(BuildContext[] files) {
        //System.out.println("PROCESSANNOTATIONS ");
        super.processAnnotations(files);
    }

    public void reconcile(ReconcileContext context) {
        //System.out.println("RECONCILE " + context.toString());
        super.reconcile(context);
    }

}
