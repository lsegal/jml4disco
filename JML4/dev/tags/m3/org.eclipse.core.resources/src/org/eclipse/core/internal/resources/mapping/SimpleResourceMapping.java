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
package org.eclipse.core.internal.resources.mapping;

import org.eclipse.core.resources.*;
import org.eclipse.core.resources.mapping.*;
import org.eclipse.core.runtime.IProgressMonitor;

/**
 * A simple resource mapping for converting IResource to ResourceMapping.
 * It uses the resource as the model object and traverses deeply.
 * 
 * @since 3.1
 */
public class SimpleResourceMapping extends ResourceMapping {
	private final IResource resource;

	public SimpleResourceMapping(IResource resource) {
		this.resource = resource;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.resources.mapping.ResourceMapping#contains(org.eclipse.core.resources.mapping.ResourceMapping)
	 */
	public boolean contains(ResourceMapping mapping) {
		if (mapping.getModelProviderId().equals(this.getModelProviderId())) {
			Object object = mapping.getModelObject();
			if (object instanceof IResource) {
				IResource other = (IResource) object;
				return resource.getFullPath().isPrefixOf(other.getFullPath());
			}
			if (object instanceof ShallowContainer) {
				ShallowContainer sc = (ShallowContainer) object;
				IResource other = sc.getResource();
				return resource.getFullPath().isPrefixOf(other.getFullPath());
			}
		}
		return false;
	}

	/* (non-Javadoc)
	 * Method declared on ResourceMapping.
	 */
	public Object getModelObject() {
		return resource;
	}

	public String getModelProviderId() {
		return ModelProvider.RESOURCE_MODEL_PROVIDER_ID;
	}

	/* (non-Javadoc)
	 * Method declared on ResourceMapping.
	 */
	public IProject[] getProjects() {
		if (resource.getType() == IResource.ROOT)
			return ((IWorkspaceRoot)resource).getProjects();
		return new IProject[] {resource.getProject()};
	}
	
	/* (non-Javadoc)
	 * Method declared on ResourceMapping.
	 */
	public ResourceTraversal[] getTraversals(ResourceMappingContext context, IProgressMonitor monitor) {
		if (resource.getType() == IResource.ROOT) {
			return new ResourceTraversal[] {new ResourceTraversal(((IWorkspaceRoot)resource).getProjects(), IResource.DEPTH_INFINITE, IResource.NONE)};
		}
		return new ResourceTraversal[] {new ResourceTraversal(new IResource[] {resource}, IResource.DEPTH_INFINITE, IResource.NONE)};
	}
}
