/*******************************************************************************
 * Copyright (c) 2005, 2006 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.core.resources.mapping;

import java.util.*;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.*;

/**
 * A resource mapping that obtains the traversals for its model object
 * from a set of child mappings.
 * <p>
 * This class is not intended to be subclasses by clients.
 * 
 * @since 3.2
 */
public final class CompositeResourceMapping extends ResourceMapping {

	private final ResourceMapping[] mappings;
	private final Object modelObject;
	private IProject[] projects;
	private String providerId;

	/**
	 * Create a composite mapping that obtains its traversals from a set of sub-mappings.
	 * @param modelObject the model object for this mapping
	 * @param mappings the sub-mappings from which the traversals are obtained
	 */
	public CompositeResourceMapping(String providerId, Object modelObject, ResourceMapping[] mappings) {
		this.modelObject = modelObject;
		this.mappings = mappings;
		this.providerId = providerId;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.mapping.ResourceMapping#contains(org.eclipse.core.resources.mapping.ResourceMapping)
	 */
	public boolean contains(ResourceMapping mapping) {
		for (int i = 0; i < mappings.length; i++) {
			ResourceMapping childMapping = mappings[i];
			if (childMapping.contains(mapping)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Return the resource mappings contained in this composite.
	 * @return Return the resource mappings contained in this composite.
	 */
	public ResourceMapping[] getMappings() {
		return mappings;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.mapping.ResourceMapping#getModelObject()
	 */
	public Object getModelObject() {
		return modelObject;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.mapping.ResourceMapping#getModelProviderId()
	 */
	public String getModelProviderId() {
		return providerId;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.mapping.ResourceMapping#getProjects()
	 */
	public IProject[] getProjects() {
		if (projects == null) {
			Set result = new HashSet();
			for (int i = 0; i < mappings.length; i++) {
				ResourceMapping mapping = mappings[i];
				result.addAll(Arrays.asList(mapping.getProjects()));
			}
			projects = (IProject[]) result.toArray(new IProject[result.size()]);
		}
		return projects;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.mapping.ResourceMapping#getTraversals(org.eclipse.core.internal.resources.mapping.ResourceMappingContext, org.eclipse.core.runtime.IProgressMonitor)
	 */
	public ResourceTraversal[] getTraversals(ResourceMappingContext context, IProgressMonitor monitor) throws CoreException {
		if (monitor == null)
			monitor = new NullProgressMonitor();
		try {
			monitor.beginTask("", 100 * mappings.length); //$NON-NLS-1$
			List result = new ArrayList();
			for (int i = 0; i < mappings.length; i++) {
				ResourceMapping mapping = mappings[i];
				result.addAll(Arrays.asList(mapping.getTraversals(context, new SubProgressMonitor(monitor, 100))));
			}
			return (ResourceTraversal[]) result.toArray(new ResourceTraversal[result.size()]);
		} finally {
			monitor.done();
		}
	}

}
