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

import java.util.HashMap;
import java.util.Map;
import org.eclipse.core.internal.utils.Policy;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.mapping.IModelProviderDescriptor;
import org.eclipse.core.resources.mapping.ModelProvider;
import org.eclipse.core.runtime.*;

public class ModelProviderManager {

	private static Map descriptors;
	private static ModelProviderManager instance;

	public synchronized static ModelProviderManager getDefault() {
		if (instance == null) {
			instance = new ModelProviderManager();
		}
		return instance;
	}

	private void detectCycles() {
		// TODO Auto-generated method stub

	}

	public IModelProviderDescriptor getDescriptor(String id) {
		lazyInitialize();
		return (IModelProviderDescriptor) descriptors.get(id);
	}

	public IModelProviderDescriptor[] getDescriptors() {
		lazyInitialize();
		return (IModelProviderDescriptor[]) descriptors.values().toArray(new IModelProviderDescriptor[descriptors.size()]);
	}

	public ModelProvider getModelProvider(String modelProviderId) throws CoreException {
		IModelProviderDescriptor desc = getDescriptor(modelProviderId);
		if (desc == null)
			return null;
		return desc.getModelProvider();
	}

	protected void lazyInitialize() {
		if (descriptors != null)
			return;
		IExtensionPoint point = Platform.getExtensionRegistry().getExtensionPoint(ResourcesPlugin.PI_RESOURCES, ResourcesPlugin.PT_MODEL_PROVIDERS);
		IExtension[] extensions = point.getExtensions();
		descriptors = new HashMap(extensions.length * 2 + 1);
		for (int i = 0, imax = extensions.length; i < imax; i++) {
			IModelProviderDescriptor desc = null;
			try {
				desc = new ModelProviderDescriptor(extensions[i]);
			} catch (CoreException e) {
				Policy.log(e);
			}
			if (desc != null)
				descriptors.put(desc.getId(), desc);
		}
		//do cycle detection now so it only has to be done once
		//cycle detection on a graph subset is a pain
		detectCycles();
	}

}
