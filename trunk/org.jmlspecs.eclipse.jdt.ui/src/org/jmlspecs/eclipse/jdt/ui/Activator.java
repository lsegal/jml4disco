package org.jmlspecs.eclipse.jdt.ui;

/** Auto-generated class, modified.
 * Author: David Cok
 * 13 September 2007
 */

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IStartup;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;
import org.jmlspecs.eclipse.jdt.internal.esc2.EscJava2Wrapper;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin implements IStartup {

	// The plug-in ID
	public static final String PLUGIN_ID = "org.jmlspecs.eclipse.jdt.ui"; //$NON-NLS-1$

	// The shared instance
	private static Activator plugin;
	
	/**
	 * The constructor
	 */
	public Activator() { /* this space intentionally has only this comment */ }

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
        init(this);
    }
	
	/** Using early startup forces this plugin to be loaded when Eclipse
	 * starts.  That gets the console initiated so that output goes to the
	 * application console rather than to the parent console or into the
	 * bitbucket.  This method and the IStartup interface are not needed if
	 * we no longer use the org.eclipse.ui.startup extension point for this
	 * plugin.
	 */
	public void earlyStartup() {
	    /* this space intentionally has only this comment */
	}
    
    private static void init(Activator a) {
        // Initialize the compiler for ESC
        Console.createLog("JML4: tool console",a);
        Log.initializeState(true); // tracing and debugging output
    }

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return plugin;
	}

	/**
	 * Returns an image descriptor for the image file at the given
	 * plug-in relative path
	 *
	 * @param path the path
	 * @return the image descriptor
	 */
	public static ImageDescriptor getImageDescriptor(String path) {
		return imageDescriptorFromPlugin(PLUGIN_ID, path);
	}
}
