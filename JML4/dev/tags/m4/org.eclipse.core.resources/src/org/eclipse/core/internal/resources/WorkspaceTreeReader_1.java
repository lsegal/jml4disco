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
package org.eclipse.core.internal.resources;

import java.io.*;
import java.util.*;
import org.eclipse.core.internal.events.BuilderPersistentInfo;
import org.eclipse.core.internal.utils.Messages;
import org.eclipse.core.internal.utils.Policy;
import org.eclipse.core.internal.watson.ElementTree;
import org.eclipse.core.internal.watson.ElementTreeReader;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceStatus;
import org.eclipse.core.runtime.*;

/**
 * Reads version 1 of the workspace tree file format.
 */
public class WorkspaceTreeReader_1 extends WorkspaceTreeReader {
	protected Workspace workspace;

	public WorkspaceTreeReader_1(Workspace workspace) {
		this.workspace = workspace;
	}

	protected int getVersion() {
		return ICoreConstants.WORKSPACE_TREE_VERSION_1;
	}

	protected void linkBuildersToTrees(List buildersToBeLinked, ElementTree[] trees, int index, IProgressMonitor monitor) {
		monitor = Policy.monitorFor(monitor);
		try {
			ArrayList infos = null;
			String projectName = null;
			for (int i = 0; i < buildersToBeLinked.size(); i++) {
				BuilderPersistentInfo info = (BuilderPersistentInfo) buildersToBeLinked.get(i);
				if (!info.getProjectName().equals(projectName)) {
					if (infos != null) { // if it is not the first iteration
						IProject project = workspace.getRoot().getProject(projectName);
						workspace.getBuildManager().setBuildersPersistentInfo(project, infos);
					}
					projectName = info.getProjectName();
					infos = new ArrayList(5);
				}
				info.setLastBuildTree(trees[index++]);
				infos.add(info);
			}
			if (infos != null) {
				IProject project = workspace.getRoot().getProject(projectName);
				workspace.getBuildManager().setBuildersPersistentInfo(project, infos);
			}
		} finally {
			monitor.done();
		}
	}

	protected void linkPluginsSavedStateToTrees(List states, ElementTree[] trees, IProgressMonitor monitor) {
		monitor = Policy.monitorFor(monitor);
		try {
			for (int i = 0; i < states.size(); i++) {
				SavedState state = (SavedState) states.get(i);
				// If the tree is too old (depends on the policy), the plug-in should not
				// get it back as a delta. It is expensive to maintain this information too long.
				final SaveManager saveManager = workspace.getSaveManager();
				if (!saveManager.isOldPluginTree(state.pluginId)) {
					state.oldTree = trees[i];
				} else {
					//clear information for this plugin from master table
					saveManager.clearDeltaExpiration(state.pluginId);
				}
			}
		} finally {
			monitor.done();
		}
	}

	protected BuilderPersistentInfo readBuilderInfo(IProject project, DataInputStream input, int index) throws IOException {
		//read the project name
		String projectName = input.readUTF();
		//use the name of the project handle if available
		if (project != null)
			projectName = project.getName();
		String builderName = input.readUTF();
		return new BuilderPersistentInfo(projectName, builderName, index);
	}

	protected void readBuildersPersistentInfo(IProject project, DataInputStream input, List builders, IProgressMonitor monitor) throws IOException {
		monitor = Policy.monitorFor(monitor);
		try {
			int builderCount = input.readInt();
			for (int i = 0; i < builderCount; i++)
				builders.add(readBuilderInfo(project, input, i));
		} finally {
			monitor.done();
		}
	}

	protected void readPluginsSavedStates(DataInputStream input, HashMap savedStates, List plugins, IProgressMonitor monitor) throws IOException, CoreException {
		monitor = Policy.monitorFor(monitor);
		try {
			int stateCount = input.readInt();
			for (int i = 0; i < stateCount; i++) {
				String pluginId = input.readUTF();
				SavedState state = new SavedState(workspace, pluginId, null, null);
				savedStates.put(pluginId, state);
				plugins.add(state);
			}
		} finally {
			monitor.done();
		}
	}

	public ElementTree readSnapshotTree(DataInputStream input, ElementTree complete, IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		String message;
		try {
			message = Messages.resources_readingSnap;
			monitor.beginTask(message, Policy.totalWork);
			ElementTreeReader reader = new ElementTreeReader(workspace.getSaveManager());
			while (input.available() > 0) {
				readWorkspaceFields(input, Policy.subMonitorFor(monitor, Policy.totalWork / 2));
				complete = reader.readDelta(complete, input);
				try {
					// make sure each snapshot is read by the correct reader
					int version = input.readInt();
					if (version != getVersion())
						return WorkspaceTreeReader.getReader(workspace, version).readSnapshotTree(input, complete, monitor);
				} catch (EOFException e) {
					break;
				}
			}
			return complete;
		} catch (IOException e) {
			message = Messages.resources_readWorkspaceSnap;
			throw new ResourceException(IResourceStatus.FAILED_READ_METADATA, null, message, e);
		} finally {
			monitor.done();
		}
	}

	public void readTree(DataInputStream input, IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		String message;
		try {
			message = Messages.resources_reading;
			monitor.beginTask(message, Policy.totalWork);
			readWorkspaceFields(input, Policy.subMonitorFor(monitor, Policy.opWork * 20 / 100));

			HashMap savedStates = new HashMap(20);
			List pluginsToBeLinked = new ArrayList(20);
			readPluginsSavedStates(input, savedStates, pluginsToBeLinked, Policy.subMonitorFor(monitor, Policy.opWork * 10 / 100));
			workspace.getSaveManager().setPluginsSavedState(savedStates);

			List buildersToBeLinked = new ArrayList(20);
			readBuildersPersistentInfo(null, input, buildersToBeLinked, Policy.subMonitorFor(monitor, Policy.opWork * 10 / 100));

			ElementTree[] trees = readTrees(Path.ROOT, input, Policy.subMonitorFor(monitor, Policy.opWork * 40 / 100));
			linkPluginsSavedStateToTrees(pluginsToBeLinked, trees, Policy.subMonitorFor(monitor, Policy.opWork * 10 / 100));
			linkBuildersToTrees(buildersToBeLinked, trees, pluginsToBeLinked.size(), Policy.subMonitorFor(monitor, Policy.opWork * 10 / 100));

		} catch (IOException e) {
			message = Messages.resources_readWorkspaceTree;
			throw new ResourceException(IResourceStatus.FAILED_READ_METADATA, null, message, e);
		} finally {
			monitor.done();
		}
	}

	public void readTree(IProject project, DataInputStream input, IProgressMonitor monitor) throws CoreException {
		monitor = Policy.monitorFor(monitor);
		String message;
		try {
			message = Messages.resources_reading;
			monitor.beginTask(message, 10);
			/* read the number of builders */
			int numBuilders = input.readInt();

			/* read in the list of builder names */
			String[] builderNames = new String[numBuilders];
			for (int i = 0; i < numBuilders; i++) {
				String builderName = input.readUTF();
				builderNames[i] = builderName;
			}
			monitor.worked(1);

			/* read and link the trees */
			ElementTree[] trees = readTrees(project.getFullPath(), input, Policy.subMonitorFor(monitor, 8));

			/* map builder names to trees */
			if (numBuilders > 0) {
				ArrayList infos = new ArrayList(trees.length * 2 + 1);
				for (int i = 0; i < numBuilders; i++) {
					BuilderPersistentInfo info = new BuilderPersistentInfo(project.getName(), builderNames[i], -1);
					info.setLastBuildTree(trees[i]);
					infos.add(info);
				}
				workspace.getBuildManager().setBuildersPersistentInfo(project, infos);
			}
			monitor.worked(1);

		} catch (IOException e) {
			message = Messages.resources_readProjectTree;
			throw new ResourceException(IResourceStatus.FAILED_READ_METADATA, null, message, e);
		} finally {
			monitor.done();
		}
	}

	/**
	 * Read trees from disk and link them to the workspace tree.
	 */
	protected ElementTree[] readTrees(IPath root, DataInputStream input, IProgressMonitor monitor) throws IOException {
		monitor = Policy.monitorFor(monitor);
		try {
			String message = Messages.resources_reading;
			monitor.beginTask(message, 4);
			ElementTreeReader treeReader = new ElementTreeReader(workspace.getSaveManager());
			ElementTree[] trees = treeReader.readDeltaChain(input);
			monitor.worked(3);
			if (root.isRoot()) {
				//Don't need to link because we're reading the whole workspace.
				//The last tree in the chain is the complete tree.
				ElementTree newTree = trees[trees.length - 1];
				newTree.setTreeData(workspace.tree.getTreeData());
				workspace.tree = newTree;
			} else {
				//splice the restored tree into the current set of trees
				workspace.linkTrees(root, trees);
			}
			monitor.worked(1);
			return trees;
		} finally {
			monitor.done();
		}
	}

	protected void readWorkspaceFields(DataInputStream input, IProgressMonitor monitor) throws IOException, CoreException {
		monitor = Policy.monitorFor(monitor);
		try {
			// read the node id 
			workspace.nextNodeId = input.readLong();
			// read the modification stamp (no longer used)
			input.readLong();
			// read the next marker id
			workspace.nextMarkerId = input.readLong();
			// read the synchronizer's registered sync partners
			((Synchronizer) workspace.getSynchronizer()).readPartners(input);
		} finally {
			monitor.done();
		}
	}
}
