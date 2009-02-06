/*******************************************************************************
 * Copyright (c) 2004, 2005 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.core.internal.resources;

import org.eclipse.core.internal.utils.*;
import org.eclipse.core.internal.watson.*;
import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.*;
import org.eclipse.core.runtime.content.IContentTypeManager;
import org.eclipse.core.runtime.content.IContentTypeManager.ContentTypeChangeEvent;
import org.eclipse.core.runtime.jobs.Job;
import org.osgi.framework.Bundle;

/**
 * Detects changes to content types/project preferences and 
 * broadcasts any corresponding encoding changes as resource deltas.  
 */

public class CharsetDeltaJob extends Job implements IContentTypeManager.IContentTypeChangeListener {

	// this is copied in the runtime tests - if changed here, has to be changed there too 
	public final static String FAMILY_CHARSET_DELTA = ResourcesPlugin.PI_RESOURCES + "charsetJobFamily"; //$NON-NLS-1$

	interface ICharsetListenerFilter {

		/**
		 * Returns the path for the node in the tree we are interested in.
		 */
		IPath getRoot();

		/**
		 * Returns whether the corresponding resource is affected by this change.
		 */
		boolean isAffected(ResourceInfo info, IPathRequestor requestor);
	}

	private ThreadLocal disabled = new ThreadLocal();

	private final Bundle systemBundle = Platform.getBundle("org.eclipse.osgi"); //$NON-NLS-1$
	private Queue work = new Queue();

	Workspace workspace;

	private static final int CHARSET_DELTA_DELAY = 500;

	public CharsetDeltaJob(Workspace workspace) {
		super(Messages.resources_charsetBroadcasting);
		this.workspace = workspace;
	}

	private void addToQueue(ICharsetListenerFilter filter) {
		synchronized (work) {
			work.add(filter);
		}
		schedule(CHARSET_DELTA_DELAY);
	}

	public boolean belongsTo(Object family) {
		return FAMILY_CHARSET_DELTA.equals(family);
	}

	public void charsetPreferencesChanged(final IProject project) {
		// avoid reacting to changes made by ourselves  
		if (isDisabled())
			return;
		// ensure all resources under the affected project are 
		// reported as having encoding changes
		ICharsetListenerFilter filter = new ICharsetListenerFilter() {

			public IPath getRoot() {
				// visit the project subtree
				return project.getFullPath();
			}

			public boolean isAffected(ResourceInfo info, IPathRequestor requestor) {
				// for now, mark all resources in the project as potential encoding resource changes 
				return true;
			}
		};
		addToQueue(filter);
	}

	public void contentTypeChanged(final ContentTypeChangeEvent event) {
		// check all files that may be affected by this change (taking
		// only the current content type state into account
		// dispatch a job to generate the deltas
		ICharsetListenerFilter filter = new ICharsetListenerFilter() {

			public IPath getRoot() {
				// visit all resources in the workspace
				return Path.ROOT;
			}

			public boolean isAffected(ResourceInfo info, IPathRequestor requestor) {
				if (info.getType() != IResource.FILE)
					return false;
				return event.getContentType().isAssociatedWith(requestor.requestName());
			}
		};
		addToQueue(filter);
	}

	private boolean isDisabled() {
		return disabled.get() != null;
	}

	private void processNextEvent(final ICharsetListenerFilter filter, IProgressMonitor monitor) throws CoreException {
		IElementContentVisitor visitor = new IElementContentVisitor() {
			public boolean visitElement(ElementTree tree, IPathRequestor requestor, Object elementContents) {
				ResourceInfo info = (ResourceInfo) elementContents;
				if (!filter.isAffected(info, requestor))
					return true;
				info = workspace.getResourceInfo(requestor.requestPath(), false, true);
				if (info == null)
					return false;
				info.incrementCharsetGenerationCount();
				return true;
			}
		};
		try {
			new ElementTreeIterator(workspace.getElementTree(), filter.getRoot()).iterate(visitor);
		} catch (WrappedRuntimeException e) {
			throw (CoreException) e.getTargetException();
		}
		if (monitor.isCanceled())
			throw new OperationCanceledException();
	}

	private ICharsetListenerFilter removeFromQueue() {
		synchronized (work) {
			return (ICharsetListenerFilter) work.remove();
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.internal.jobs.InternalJob#run(org.eclipse.core.runtime.IProgressMonitor)
	 */
	public IStatus run(IProgressMonitor monitor) {
		monitor = Policy.monitorFor(monitor);
		try {
			String message = Messages.resources_charsetBroadcasting;
			monitor.beginTask(message, Policy.totalWork);
			try {
				workspace.prepareOperation(null, monitor);
				workspace.beginOperation(true);
				ICharsetListenerFilter next;
				//if the system is shutting down, don't broadcast			
				while (systemBundle.getState() != Bundle.STOPPING && (next = removeFromQueue()) != null)
					processNextEvent(next, monitor);
			} catch (OperationCanceledException e) {
				workspace.getWorkManager().operationCanceled();
				return Status.CANCEL_STATUS;
			} finally {
				workspace.endOperation(null, true, Policy.subMonitorFor(monitor, Policy.endOpWork));
			}
			monitor.worked(Policy.opWork);
		} catch (CoreException sig) {
			return sig.getStatus();
		} finally {
			monitor.done();
		}
		return Status.OK_STATUS;
	}

	/**
	 * Turns off reaction to changes in the preference file.
	 */
	public void setDisabled(boolean disabled) {
		// using a thread local because this can be called by multiple threads concurrently
		this.disabled.set(disabled ? Boolean.TRUE : null);
	}

	public void shutdown() {
		Platform.getContentTypeManager().removeContentTypeChangeListener(this);
	}

	public void startup() {
		Platform.getContentTypeManager().addContentTypeChangeListener(this);
	}
}
