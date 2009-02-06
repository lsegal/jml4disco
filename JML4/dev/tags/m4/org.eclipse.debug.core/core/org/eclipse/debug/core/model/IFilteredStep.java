/*******************************************************************************
 * Copyright (c) 2000, 2005 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.debug.core.model;


import org.eclipse.debug.core.DebugException;

/**
 * Provides the ability to perform a filtered step. Implementations must be non-
 * blocking. Filter implementation is debug model specific and may not be
 * supported by all debug models.
 * <p>
 * Clients may implement this interface.
 * </p>
 * @since 2.1
 * @deprecated clients should implement <code>IStepFilters</code> instead
 */
public interface IFilteredStep extends IStep {
	/**
	 * Returns whether this element can currently perform a filtered step into.
	 *
	 * @return whether this element can currently perform a filtered step into
	 */
	public boolean canStepWithFilters();
	/**
	 * Steps into the current statement, generating <code>RESUME</code>
	 * and <code>SUSPEND</code> events for the associated thread, applying step
	 * filters, as applicable for the associated thread. Can only be called when
	 * the associated thread is suspended. Implementations must implement
	 * stepping as non- blocking.
	 *
	 * @exception DebugException on failure. Reasons include:<ul>
	 * <li>TARGET_REQUEST_FAILED - The request failed in the target</li>
	 * <li>NOT_SUPPORTED - The capability is not supported by the target</li>
	 * </ul>
	 */
	public void stepWithFilters() throws DebugException;
}
