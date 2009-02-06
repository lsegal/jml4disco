/*******************************************************************************
 * Copyright (c) 2000, 2007 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.debug.internal.core;

 
import java.io.IOException;

import org.eclipse.debug.core.model.IStreamMonitor;
import org.eclipse.debug.core.model.IStreamsProxy;
import org.eclipse.debug.core.model.IStreamsProxy2;

/**
 * Standard implementation of a streams proxy for s 
 * StreamsProxy
 */

public class StreamsProxy implements IStreamsProxy, IStreamsProxy2 {
	/**
	 * The monitor for the output stream (connected to standard out of the process)
	 */
	private OutputStreamMonitor fOutputMonitor;
	/**
	 * The monitor for the error stream (connected to standard error of the process)
	 */
	private OutputStreamMonitor fErrorMonitor;
	/**
	 * The monitor for the input stream (connected to standard in of the process)
	 */
	private InputStreamMonitor fInputMonitor;
	/**
	 * Records the open/closed state of communications with
	 * the underlying streams.
	 */
	private boolean fClosed= false;
	/**
	 * Creates a <code>StreamsProxy</code> on the streams
	 * of the given system process.
	 * 
	 * @param process system process to create a streams proxy on
	 * @param encoding the process's encoding or <code>null</code> if default
	 */
	public StreamsProxy(Process process, String encoding) {
		if (process == null) {
			return;
		}
		fOutputMonitor= new OutputStreamMonitor(process.getInputStream(), encoding);
		fErrorMonitor= new OutputStreamMonitor(process.getErrorStream(), encoding);
		fInputMonitor= new InputStreamMonitor(process.getOutputStream());
		fOutputMonitor.startMonitoring();
		fErrorMonitor.startMonitoring();
		fInputMonitor.startMonitoring();
	}

	/**
	 * Causes the proxy to close all
	 * communications between it and the
	 * underlying streams after all remaining data
	 * in the streams is read.
	 */
	public void close() {
		if (!fClosed) {
			fClosed= true;
			fOutputMonitor.close();
			fErrorMonitor.close();
			fInputMonitor.close();
		}
	}

	/**
	 * Causes the proxy to close all
	 * communications between it and the
	 * underlying streams immediately.
	 * Data remaining in the streams is lost.
	 */	
	public void kill() {
		fClosed= true;
		fOutputMonitor.kill();
		fErrorMonitor.kill();
		fInputMonitor.close();
	}

	/**
	 * @see IStreamsProxy#getErrorStreamMonitor()
	 */
	public IStreamMonitor getErrorStreamMonitor() {
		return fErrorMonitor;
	}

	/**
	 * @see IStreamsProxy#getOutputStreamMonitor()
	 */
	public IStreamMonitor getOutputStreamMonitor() {
		return fOutputMonitor;
	}

	/**
	 * @see IStreamsProxy#write(String)
	 */
	public void write(String input) throws IOException {
		if (!fClosed) {
			fInputMonitor.write(input);
		} else {
			throw new IOException();
		}
	}

    /* (non-Javadoc)
     * @see org.eclipse.debug.core.model.IStreamsProxy2#closeInputStream()
     */
    public void closeInputStream() throws IOException {
        if (!fClosed) {
            fInputMonitor.closeInputStream();
        } else {
            throw new IOException();
        }
        
    }

}
