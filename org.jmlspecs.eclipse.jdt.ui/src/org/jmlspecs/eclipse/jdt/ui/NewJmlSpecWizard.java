package org.jmlspecs.eclipse.jdt.ui;

import java.net.URL;

import org.eclipse.jdt.internal.ui.wizards.NewClassCreationWizard;
import org.eclipse.jdt.internal.ui.wizards.NewElementWizard;
import org.eclipse.jdt.internal.ui.wizards.NewWizardMessages;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;

import org.eclipse.jdt.core.IJavaElement;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;

import org.eclipse.jdt.ui.wizards.NewClassWizardPage;

import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.JavaPluginImages;
import org.eclipse.jface.resource.ImageDescriptor;
import org.osgi.framework.Bundle;

// This was started from NewClassCreationWizard

public class NewJmlSpecWizard extends NewElementWizard {

        private NewJmlSpecCreationPage fPage;
        private boolean fOpenEditorOnFinish;
        
        public static final ImageDescriptor NEWSPEC = create("icons/jml-logo-small.png",true);            //$NON-NLS-1$

        /*
         * Creates an image descriptor for the given prefix and name in the JDT UI bundle. The path can
         * contain variables like $NL$.
         * If no image could be found, <code>useMissingImageDescriptor</code> decides if either
         * the 'missing image descriptor' is returned or <code>null</code>.
         * or <code>null</code>.
         */
        private static ImageDescriptor create(String name, boolean useMissingImageDescriptor) {
            IPath path= new Path(name);
            Bundle bundle = Activator.getDefault().getBundle();
            URL url= FileLocator.find(bundle, path, null);
            if (url != null) {
                return ImageDescriptor.createFromURL(url);
            }
            if (useMissingImageDescriptor) {
                return ImageDescriptor.getMissingImageDescriptor();
            }
            return null;
        }

        public NewJmlSpecWizard(NewJmlSpecCreationPage page, boolean openEditorOnFinish) {
            setDefaultPageImageDescriptor(NEWSPEC);
            //setDialogSettings(JavaPlugin.getDefault().getDialogSettings()); // FIXME - do something to remeber dialog settings between invocations?
            setWindowTitle("New Jml Specification File");
            
            fPage= page;
            fOpenEditorOnFinish= openEditorOnFinish;
        }
        
        public NewJmlSpecWizard() {
            this(null, true);
        }
        
        /*
         * @see Wizard#createPages
         */ 
        public void addPages() {
            super.addPages();
            if (fPage == null) {
                fPage= new NewJmlSpecCreationPage();
                fPage.init(getSelection());
            }
            addPage(fPage);
        }
        
        /*(non-Javadoc)
         * @see org.eclipse.jdt.internal.ui.wizards.NewElementWizard#canRunForked()
         */
        protected boolean canRunForked() {
            return !fPage.isEnclosingTypeSelected();
        }

        /* (non-Javadoc)
         * @see org.eclipse.jdt.internal.ui.wizards.NewElementWizard#finishPage(org.eclipse.core.runtime.IProgressMonitor)
         */
        protected void finishPage(IProgressMonitor monitor) throws InterruptedException, CoreException {
            fPage.createType(monitor); // use the full progress monitor
        }
            
        /* (non-Javadoc)
         * @see org.eclipse.jface.wizard.IWizard#performFinish()
         */
        public boolean performFinish() {
            warnAboutTypeCommentDeprecation();
            boolean res= super.performFinish();
            if (res) {
                IResource resource= fPage.getModifiedResource();
                if (resource != null) {
                    selectAndReveal(resource);
                    if (fOpenEditorOnFinish) {
                        openResource((IFile) resource);
                    }
                }   
            }
            return res;
        }

        /* (non-Javadoc)
         * @see org.eclipse.jdt.internal.ui.wizards.NewElementWizard#getCreatedElement()
         */
        public IJavaElement getCreatedElement() {
            return fPage.getCreatedType();
        }

        
    }

