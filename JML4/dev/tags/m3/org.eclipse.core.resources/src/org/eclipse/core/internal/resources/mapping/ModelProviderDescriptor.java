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

import java.util.*;
import org.eclipse.core.expressions.*;
import org.eclipse.core.internal.resources.ResourceException;
import org.eclipse.core.internal.utils.Messages;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.mapping.*;
import org.eclipse.core.runtime.*;
import org.eclipse.osgi.util.NLS;

public class ModelProviderDescriptor implements IModelProviderDescriptor {

	private String id;
	private String[] extendedModels;
	private String label;
	private ModelProvider provider;
	private Expression enablementRule;

	private static EvaluationContext createEvaluationContext(Object element) {
		EvaluationContext result = new EvaluationContext(null, element);
		return result;
	}

	public ModelProviderDescriptor(IExtension extension) throws CoreException {
		readExtension(extension);
	}

	private boolean convert(EvaluationResult eval) {
		if (eval == EvaluationResult.FALSE)
			return false;
		return true;
	}

	protected void fail(String reason) throws CoreException {
		throw new ResourceException(new Status(IStatus.ERROR, ResourcesPlugin.PI_RESOURCES, 1, reason, null));
	}

	public String[] getExtendedModels() {
		return extendedModels;
	}

	public String getId() {
		return id;
	}

	public String getLabel() {
		return label;
	}

	public IResource[] getMatchingResources(IResource[] resources) throws CoreException {
		Set result = new HashSet();
		for (int i = 0; i < resources.length; i++) {
			IResource resource = resources[i];
			EvaluationContext evalContext = createEvaluationContext(resource);
			if (matches(evalContext)) {
				result.add(resource);
			}
		}
		return (IResource[]) result.toArray(new IResource[result.size()]);
	}

	public synchronized ModelProvider getModelProvider() throws CoreException {
		if (provider == null) {
			IExtension extension = Platform.getExtensionRegistry().getExtension(ResourcesPlugin.PI_RESOURCES, ResourcesPlugin.PT_MODEL_PROVIDERS, id);
			IConfigurationElement[] elements = extension.getConfigurationElements();
			for (int i = 0; i < elements.length; i++) {
				IConfigurationElement element = elements[i];
				if (element.getName().equalsIgnoreCase("modelProvider")) { //$NON-NLS-1$
					try {
						provider = (ModelProvider) element.createExecutableExtension("class"); //$NON-NLS-1$
						provider.init(this);
					} catch (ClassCastException e) {
						String message = NLS.bind(Messages.mapping_wrongType, id);
						throw new CoreException(new Status(IStatus.ERROR, ResourcesPlugin.PI_RESOURCES, Platform.PLUGIN_ERROR, message, e));
					}
				}
			}
		}
		return provider;
	}

	public boolean matches(IEvaluationContext context) throws CoreException {
		if (enablementRule == null)
			return false;
		return convert(enablementRule.evaluate(context));
	}

	/**
	 * Initialize this descriptor based on the provided extension point.
	 */
	protected void readExtension(IExtension extension) throws CoreException {
		//read the extension
		id = extension.getUniqueIdentifier();
		if (id == null)
			fail(Messages.mapping_noIdentifier);
		label = extension.getLabel();
		IConfigurationElement[] elements = extension.getConfigurationElements();
		int count = elements.length;
		ArrayList extendsList = new ArrayList(count);
		for (int i = 0; i < count; i++) {
			IConfigurationElement element = elements[i];
			String name = element.getName();
			if (name.equalsIgnoreCase("extends-model")) { //$NON-NLS-1$
				String attribute = element.getAttribute("id"); //$NON-NLS-1$
				if (attribute == null)
					fail(NLS.bind(Messages.mapping_invalidDef, id));
				extendsList.add(attribute);
			} else if (name.equalsIgnoreCase(ExpressionTagNames.ENABLEMENT)) {
				enablementRule = ExpressionConverter.getDefault().perform(element);
			}
		}
		extendedModels = (String[]) extendsList.toArray(new String[extendsList.size()]);
	}

	public ResourceTraversal[] getMatchingTraversals(ResourceTraversal[] traversals) throws CoreException {
		List result = new ArrayList();
		for (int i = 0; i < traversals.length; i++) {
			ResourceTraversal traversal = traversals[i];
			if (getMatchingResources(traversal.getResources()).length > 0) {
				result.add(traversal);
			}
		}
		return (ResourceTraversal[]) result.toArray(new ResourceTraversal[result.size()]);
	}

}
