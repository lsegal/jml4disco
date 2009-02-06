/*******************************************************************************
 * Copyright (c) 2002, 2007 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM - Initial API and implementation
 *******************************************************************************/
package org.eclipse.core.internal.resources.refresh.win32;

import java.io.File;
import java.util.*;
import org.eclipse.core.internal.refresh.RefreshManager;
import org.eclipse.core.internal.utils.Messages;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.refresh.IRefreshMonitor;
import org.eclipse.core.resources.refresh.IRefreshResult;
import org.eclipse.core.runtime.*;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.osgi.util.NLS;
import org.osgi.framework.Bundle;

/**
 * A monitor that works on Win32 platforms. Provides simple notification of
 * entire trees by reporting that the root of the tree has changed to depth
 * DEPTH_INFINITE.
 */
class Win32Monitor extends Job implements IRefreshMonitor {
	private static final long RESCHEDULE_DELAY = 1000;

	/**
	 * A ChainedHandle is a linked list of handles.
	 */
	protected abstract class ChainedHandle extends Handle {
		private ChainedHandle next;
		private ChainedHandle previous;

		public abstract boolean exists();

		public ChainedHandle getNext() {
			return next;
		}

		public ChainedHandle getPrevious() {
			return previous;
		}

		public void setNext(ChainedHandle next) {
			this.next = next;
		}

		public void setPrevious(ChainedHandle previous) {
			this.previous = previous;
		}
	}

	protected class FileHandle extends ChainedHandle {
		private File file;

		public FileHandle(File file) {
			this.file = file;
		}

		public boolean exists() {
			return file.exists();
		}

		public void handleNotification() {
			if (!isOpen())
				return;
			ChainedHandle next = getNext();
			if (next != null) {
				if (next.isOpen()) {
					if (!next.exists()) {
						if (next instanceof LinkedResourceHandle) {
							next.close();
							LinkedResourceHandle linkedResourceHandle = (LinkedResourceHandle) next;
							linkedResourceHandle.postRefreshRequest();
						} else {
							next.close();
						}
						ChainedHandle previous = getPrevious();
						if (previous != null)
							previous.open();
					}
				} else {
					next.open();
					if (next.isOpen()) {
						Handle previous = getPrevious();
						previous.close();
						if (next instanceof LinkedResourceHandle)
							((LinkedResourceHandle) next).postRefreshRequest();
					}
				}
			}
			findNextChange();
		}

		public void open() {
			if (!isOpen()) {
				Handle next = getNext();
				if (next != null && next.isOpen()) {
					openHandleOn(file);
				} else {
					if (exists()) {
						openHandleOn(file);
					}
					Handle previous = getPrevious();
					if (previous != null) {
						previous.open();
					}
				}
			}
		}
	}

	protected abstract class Handle {
		protected long handleValue;

		public Handle() {
			handleValue = Win32Natives.INVALID_HANDLE_VALUE;
		}

		public void close() {
			if (isOpen()) {
				if (!Win32Natives.FindCloseChangeNotification(handleValue)) {
					int error = Win32Natives.GetLastError();
					if (error != Win32Natives.ERROR_INVALID_HANDLE)
						addException(NLS.bind(Messages.WM_errCloseHandle, Integer.toString(error)));
				}
				if (RefreshManager.DEBUG)
					System.out.println(DEBUG_PREFIX + "removed handle: " + handleValue); //$NON-NLS-1$
				handleValue = Win32Natives.INVALID_HANDLE_VALUE;
			}
		}

		private long createHandleValue(String path, boolean monitorSubtree, int flags) {
			long handle = Win32Natives.FindFirstChangeNotification(path, monitorSubtree, flags);
			if (handle == Win32Natives.INVALID_HANDLE_VALUE) {
				int error = Win32Natives.GetLastError();
				addException(NLS.bind(Messages.WM_errCreateHandle, path, Integer.toString(error)));
			}
			return handle;
		}

		public void destroy() {
			close();
		}

		protected void findNextChange() {
			if (!Win32Natives.FindNextChangeNotification(handleValue)) {
				int error = Win32Natives.GetLastError();
				if (error != Win32Natives.ERROR_INVALID_HANDLE && error != Win32Natives.ERROR_SUCCESS) {
					addException(NLS.bind(Messages.WM_errFindChange, Integer.toString(error)));
				}
				removeHandle(this);
			}
		}

		public long getHandleValue() {
			return handleValue;
		}

		public abstract void handleNotification();

		public boolean isOpen() {
			return handleValue != Win32Natives.INVALID_HANDLE_VALUE;
		}

		public abstract void open();

		protected void openHandleOn(File file) {
			openHandleOn(file.getAbsolutePath(), false);
		}

		protected void openHandleOn(IResource resource) {
			openHandleOn(resource.getLocation().toOSString(), true);
		}

		private void openHandleOn(String path, boolean subtree) {
			setHandleValue(createHandleValue(path, subtree, Win32Natives.FILE_NOTIFY_CHANGE_FILE_NAME | Win32Natives.FILE_NOTIFY_CHANGE_DIR_NAME | Win32Natives.FILE_NOTIFY_CHANGE_LAST_WRITE | Win32Natives.FILE_NOTIFY_CHANGE_SIZE));
			if (isOpen()) {
				fHandleValueToHandle.put(new Long(getHandleValue()), this);
				setHandleValueArrays(createHandleArrays());
			} else {
				close();
			}
		}

		protected void postRefreshRequest(IResource resource) {
			//native callback occurs even if resource was changed within workspace
			if (!resource.isSynchronized(IResource.DEPTH_INFINITE))
				refreshResult.refresh(resource);
		}

		public void setHandleValue(long handleValue) {
			this.handleValue = handleValue;
		}
	}

	protected class LinkedResourceHandle extends ChainedHandle {
		private List fileHandleChain;
		private IResource resource;

		/**
		 * @param resource
		 */
		public LinkedResourceHandle(IResource resource) {
			this.resource = resource;
			createFileHandleChain();
		}

		protected void createFileHandleChain() {
			fileHandleChain = new ArrayList(1);
			File file = new File(resource.getLocation().toOSString());
			file = file.getParentFile();
			while (file != null) {
				fileHandleChain.add(0, new FileHandle(file));
				file = file.getParentFile();
			}
			int size = fileHandleChain.size();
			for (int i = 0; i < size; i++) {
				ChainedHandle handle = (ChainedHandle) fileHandleChain.get(i);
				handle.setPrevious((i > 0) ? (ChainedHandle) fileHandleChain.get(i - 1) : null);
				handle.setNext((i + 1 < size) ? (ChainedHandle) fileHandleChain.get(i + 1) : this);
			}
			setPrevious((size > 0) ? (ChainedHandle) fileHandleChain.get(size - 1) : null);
		}

		public void destroy() {
			super.destroy();
			for (Iterator i = fileHandleChain.iterator(); i.hasNext();) {
				Handle handle = (Handle) i.next();
				handle.destroy();
			}
		}

		public boolean exists() {
			IPath location = resource.getLocation();
			return location == null ? false : location.toFile().exists();
		}

		public void handleNotification() {
			if (isOpen()) {
				postRefreshRequest(resource);
				findNextChange();
			}
		}

		public void open() {
			if (!isOpen()) {
				if (exists()) {
					openHandleOn(resource);
				}
				FileHandle handle = (FileHandle) getPrevious();
				if (handle != null && !handle.isOpen()) {
					handle.open();
				}
			}
		}

		public void postRefreshRequest() {
			postRefreshRequest(resource);
		}
	}

	protected class ResourceHandle extends Handle {
		private IResource resource;

		public ResourceHandle(IResource resource) {
			super();
			this.resource = resource;
		}

		public IResource getResource() {
			return resource;
		}

		public void handleNotification() {
			if (isOpen()) {
				postRefreshRequest(resource);
				findNextChange();
			}
		}

		public void open() {
			if (!isOpen()) {
				openHandleOn(resource);
			}
		}
	}

	private static final String DEBUG_PREFIX = "Win32RefreshMonitor: "; //$NON-NLS-1$
	private static final int WAIT_FOR_MULTIPLE_OBJECTS_TIMEOUT = 300;
	/**
	 * Any errors that have occurred
	 */
	protected MultiStatus errors;
	/**
	 * Arrays of handles, split evenly when the number of handles is larger
	 * than Win32Natives.MAXIMUM_WAIT_OBJECTS
	 */
	protected long[][] fHandleValueArrays;
	/**
	 * Mapping of handles (java.lang.Long) to absolute paths
	 * (java.lang.String).
	 */
	protected Map fHandleValueToHandle;
	protected IRefreshResult refreshResult;

	/*
	 * Creates a new monitor. @param result A result that will recieve refresh
	 * callbacks and error notifications
	 */
	public Win32Monitor(IRefreshResult result) {
		super(Messages.WM_jobName);
		this.refreshResult = result;
		setPriority(Job.DECORATE);
		setSystem(true);
		fHandleValueToHandle = new HashMap(1);
		setHandleValueArrays(createHandleArrays());
	}

	/**
	 * Logs an exception
	 */
	protected synchronized void addException(String message) {
		if (errors == null) {
			String msg = Messages.WM_errors;
			errors = new MultiStatus(ResourcesPlugin.PI_RESOURCES, 1, msg, null);
		}
		errors.add(new Status(IStatus.ERROR, ResourcesPlugin.PI_RESOURCES, 1, message, null));
	}

	/*
	 * Splits the given array into arrays of length no greater than <code> max
	 * </code> . The lengths of the sub arrays differ in size by no more than
	 * one element. <p> Examples: <ul><li> If an array of size 11 is split
	 * with a max of 4, the resulting arrays are of size 4, 4, and 3. </li>
	 * <li> If an array of size 18 is split with a max of 5, the resulting
	 * arrays are of size 5, 5, 4, and 4. </li></ul>
	 */
	private long[][] balancedSplit(final long[] array, final int max) {
		int elementCount = array.length;
		// want to handle [1, max] rather than [0, max)
		int subArrayCount = ((elementCount - 1) / max) + 1;
		int subArrayBaseLength = elementCount / subArrayCount;
		int overflow = elementCount % subArrayCount;
		long[][] result = new long[subArrayCount][];
		int count = 0;
		for (int i = 0; i < subArrayCount; i++) {
			int subArrayLength = subArrayBaseLength + (overflow-- > 0 ? 1 : 0);
			long[] subArray = new long[subArrayLength];
			for (int j = 0; j < subArrayLength; j++) {
				subArray[j] = array[count++];
			}
			result[i] = subArray;
		}
		return result;
	}

	private Handle createHandle(IResource resource) {
		if (resource.isLinked())
			return new LinkedResourceHandle(resource);
		return new ResourceHandle(resource);
	}

	/*
	 * Since the Win32Natives.WaitForMultipleObjects(...) method cannot accept
	 * more than a certain number of objects, we are forced to split the array
	 * of objects to monitor and monitor each one individually. <p> This method
	 * splits the list of handles into arrays no larger than
	 * Win32Natives.MAXIMUM_WAIT_OBJECTS. The arrays are balenced so that they
	 * differ in size by no more than one element.
	 */
	protected long[][] createHandleArrays() {
		long[] handles;
		// synchronized: in order to protect the map during iteration
		synchronized (fHandleValueToHandle) {
			Set keys = fHandleValueToHandle.keySet();
			int size = keys.size();
			if (size == 0) {
				return new long[0][0];
			}
			handles = new long[size];
			int count = 0;
			for (Iterator i = keys.iterator(); i.hasNext();) {
				handles[count++] = ((Long) i.next()).longValue();
			}
		}
		return balancedSplit(handles, Win32Natives.MAXIMUM_WAIT_OBJECTS);
	}

	private Handle getHandle(IResource resource) {
		if (resource == null) {
			return null;
		}
		// synchronized: in order to protect the map during iteration
		synchronized (fHandleValueToHandle) {
			for (Iterator i = fHandleValueToHandle.values().iterator(); i.hasNext();) {
				Handle handle = (Handle) i.next();
				if (handle instanceof ResourceHandle) {
					ResourceHandle resourceHandle = (ResourceHandle) handle;
					if (resourceHandle.getResource().equals(resource)) {
						return handle;
					}
				}
			}
		}
		return null;
	}

	/*
	 * Answers arrays of handles. The handles are split evenly when the number
	 * of handles becomes larger than Win32Natives.MAXIMUM_WAIT_OBJECTS.
	 * @return long[][]
	 */
	private long[][] getHandleValueArrays() {
		return fHandleValueArrays;
	}

	/**
	 * Adds a resource to be monitored by this native monitor
	 */
	public boolean monitor(IResource resource) {
		IPath location = resource.getLocation();
		if (location == null) {
			// cannot monitor remotely managed containers
			return false;
		}
		Handle handle = createHandle(resource);
		// synchronized: handle creation must be atomic
		synchronized (this) {
			handle.open();
		}
		if (!handle.isOpen()) {
			//ignore errors if we can't even create a handle on the resource
			//it will fall back to polling anyway
			errors = null;
			return false;
		}
		//make sure the job is running
		schedule(RESCHEDULE_DELAY);
		if (RefreshManager.DEBUG)
			System.out.println(DEBUG_PREFIX + " added monitor for: " + resource); //$NON-NLS-1$
		return true;
	}

	/**
	 * Removes the handle from the <code>fHandleValueToHandle</code> map.
	 * 
	 * @param handle
	 *                  a handle, not <code>null</code>
	 */
	protected void removeHandle(Handle handle) {
		List handles = new ArrayList(1);
		handles.add(handle);
		removeHandles(handles);
	}

	/**
	 * Removes all of the handles in the given collection from the <code>fHandleValueToHandle</code>
	 * map. If collections from the <code>fHandleValueToHandle</code> map are
	 * used, copy them before passing them in as this method modifies the
	 * <code>fHandleValueToHandle</code> map.
	 * 
	 * @param handles
	 *                  a collection of handles, not <code>null</code>
	 */
	private void removeHandles(Collection handles) {
		// synchronized: protect the array, removal must be atomic
		synchronized (this) {
			for (Iterator i = handles.iterator(); i.hasNext();) {
				Handle handle = (Handle) i.next();
				fHandleValueToHandle.remove(new Long(handle.getHandleValue()));
				handle.destroy();
			}
			setHandleValueArrays(createHandleArrays());
		}
	}

	/*
	 * @see java.lang.Runnable#run()
	 */
	protected IStatus run(IProgressMonitor monitor) {
		long start = -System.currentTimeMillis();
		if (RefreshManager.DEBUG)
			System.out.println(DEBUG_PREFIX + "job started."); //$NON-NLS-1$
		try {
			long[][] handleArrays = getHandleValueArrays();
			monitor.beginTask(Messages.WM_beginTask, handleArrays.length);
			// If changes occur to the list of handles,
			// ignore them until the next time through the loop.
			for (int i = 0, length = handleArrays.length; i < length; i++) {
				if (monitor.isCanceled())
					return Status.CANCEL_STATUS;
				waitForNotification(handleArrays[i]);
				monitor.worked(1);
			}
		} finally {
			monitor.done();
			start += System.currentTimeMillis();
			if (RefreshManager.DEBUG)
				System.out.println(DEBUG_PREFIX + "job finished in: " + start + "ms"); //$NON-NLS-1$ //$NON-NLS-2$
		}
		//always reschedule the job - so it will come back after errors or cancelation
		//make sure it doesn't hog more that 5% of CPU
		long delay = Math.max(RESCHEDULE_DELAY, start * 30);
		if (RefreshManager.DEBUG)
			System.out.println(DEBUG_PREFIX + "rescheduling in: " + delay / 1000 + " seconds"); //$NON-NLS-1$ //$NON-NLS-2$
		final Bundle bundle = Platform.getBundle(ResourcesPlugin.PI_RESOURCES);
		//if the bundle is null then the framework has shutdown - just bail out completely (bug 98219)
		if (bundle == null)
			return Status.OK_STATUS;
		//don't reschedule the job if the resources plugin has been shut down
		if (bundle.getState() == Bundle.ACTIVE)
			schedule(delay);
		MultiStatus result = errors;
		errors = null;
		//just log native refresh failures
		if (result != null && !result.isOK())
			ResourcesPlugin.getPlugin().getLog().log(result);
		return Status.OK_STATUS;
	}

	protected void setHandleValueArrays(long[][] arrays) {
		fHandleValueArrays = arrays;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.jobs.Job#shouldRun()
	 */
	public boolean shouldRun() {
		return !fHandleValueToHandle.isEmpty();
	}

	/*
	 * @see org.eclipse.core.resources.refresh.IRefreshMonitor#unmonitor(IContainer)
	 */
	public void unmonitor(IResource resource) {
		if (resource == null) {
			// resource == null means stop monitoring all resources
			synchronized (fHandleValueToHandle) {
				removeHandles(new ArrayList(fHandleValueToHandle.values()));
			}
		} else {
			Handle handle = getHandle(resource);
			if (handle != null)
				removeHandle(handle);
		}
		//stop the job if there are no more handles
		if (fHandleValueToHandle.isEmpty())
			cancel();
	}

	/**
	 * Performs the native call to wait for notification on one of the given
	 * handles.
	 * 
	 * @param handleValues
	 *                  an array of handles, it must contain no duplicates.
	 */
	private void waitForNotification(long[] handleValues) {
		int handleCount = handleValues.length;
		int index = Win32Natives.WaitForMultipleObjects(handleCount, handleValues, false, WAIT_FOR_MULTIPLE_OBJECTS_TIMEOUT);
		if (index == Win32Natives.WAIT_TIMEOUT) {
			// nothing happened.
			return;
		}
		if (index == Win32Natives.WAIT_FAILED) {
			// we ran into a problem
			int error = Win32Natives.GetLastError();
			if (error != Win32Natives.ERROR_INVALID_HANDLE && error != Win32Natives.ERROR_SUCCESS) {
				addException(NLS.bind(Messages.WM_nativeErr, Integer.toString(error)));
				refreshResult.monitorFailed(this, null);
			}
			return;
		}
		// a change occurred
		// WaitForMultipleObjects returns WAIT_OBJECT_0 + index
		index -= Win32Natives.WAIT_OBJECT_0;
		Handle handle = (Handle) fHandleValueToHandle.get(new Long(handleValues[index]));
		if (handle != null)
			handle.handleNotification();
	}
}
