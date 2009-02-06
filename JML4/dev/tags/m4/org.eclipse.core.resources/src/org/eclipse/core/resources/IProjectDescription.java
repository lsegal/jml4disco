/*******************************************************************************
 * Copyright (c) 2000, 2008 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.core.resources;

import java.net.URI;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;

/**
 * A project description contains the meta-data required to define
 * a project.  In effect, a project description is a project's "content".
 * 
 * @noimplement This interface is not intended to be implemented by clients.
 */
public interface IProjectDescription {
	/**
	 * Constant that denotes the name of the project description file (value 
	 * <code>".project"</code>). 
	 * The handle of a project's description file is 
	 * <code>project.getFile(DESCRIPTION_FILE_NAME)</code>.
	 * The project description file is located in the root of the project's content area.
	 * 
	 * @since 2.0
	 */
	public static final String DESCRIPTION_FILE_NAME = ".project"; //$NON-NLS-1$

	/**
	 * Returns the list of build commands to run when building the described project.
	 * The commands are listed in the order in which they are to be run.
	 *
	 * @return the list of build commands for the described project 
	 */
	public ICommand[] getBuildSpec();

	/**
	 * Returns the descriptive comment for the described project.
	 *
	 * @return the comment for the described project
	 */
	public String getComment();

	/**
	 * Returns the dynamic project references for the described project. Dynamic
	 * project references can be used instead of simple project references in cases
	 * where the reference information is computed dynamically be a third party.
	 * These references are persisted by the workspace in a private location outside
	 * the project description file, and as such will not be shared when a project is
	 * exported or persisted in a repository.  A client using project references
	 * is always responsible for setting these references when a project is created
	 * or recreated.
	 * <p>
	 * The returned projects need not exist in the workspace. The result will not 
	 * contain duplicates. Returns an empty array if there are no dynamic project 
	 * references on this description.
	 *
	 * @see #getReferencedProjects()
	 * @see #setDynamicReferences(IProject[])
	 * @return a list of projects
	 * @since 3.0
	 */
	public IProject[] getDynamicReferences();

	/**
	 * Returns the  local file system location for the described project.  The path
	 * will be either an absolute file system path, or a relative path whose first
	 * segment is the name of a workspace path variable. <code>null</code> is
	 * returned if the default location should be used.  This method will return 
	 * <code>null</code> if this project is not located in the local file system.
	 *
	 * @return the location for the described project or <code>null</code>
	 * @deprecated Since 3.2, project locations are not necessarily in the local file
	 * system.  The more general {@link #getLocationURI()} method should be used instead.
	 */
	public IPath getLocation();

	/**
	 * Returns the location URI for the described project.  <code>null</code> is
	 * returned if the default location should be used.
	 *
	 * @return the location for the described project or <code>null</code>
	 * @since 3.2
	 * @see #setLocationURI(URI)
	 */
	public URI getLocationURI();

	/**
	 * Returns the name of the described project.
	 *
	 * @return the name of the described project
	 */
	public String getName();

	/** 
	 * Returns the list of natures associated with the described project.
	 * Returns an empty array if there are no natures on this description.
	 *
	 * @return the list of natures for the described project
	 * @see #setNatureIds(String[])
	 */
	public String[] getNatureIds();

	/**
	 * Returns the projects referenced by the described project. These references
	 * are persisted in the project description file (&quot;.project&quot;) and as such
	 * will be shared whenever the project is exported to another workspace. For
	 * references that are likely to change from one workspace to another, dynamic
	 * references should be used instead.
	 * <p>
	 * The projects need not exist in the workspace.
	 * The result will not contain duplicates. Returns an empty
	 * array if there are no referenced projects on this description.
	 *
	 *@see #getDynamicReferences()
	 * @return a list of projects
	 */
	public IProject[] getReferencedProjects();

	/** 
	 * Returns whether the project nature specified by the given
	 * nature extension id has been added to the described project. 
	 *
	 * @param natureId the nature extension identifier
	 * @return <code>true</code> if the described project has the given nature 
	 */
	public boolean hasNature(String natureId);

	/**
	 * Returns a new build command.
	 * <p>
	 * Note that the new command does not become part of this project
	 * description's build spec until it is installed via the <code>setBuildSpec</code>
	 * method.
	 * </p>
	 *
	 * @return a new command
	 * @see #setBuildSpec(ICommand[])
	 */
	public ICommand newCommand();

	/**
	 * Sets the list of build command to run when building the described project.
	 * <p>
	 * Users must call {@link IProject#setDescription(IProjectDescription, int, IProgressMonitor)} 
	 * before changes made to this description take effect.
	 * </p>
	 *
	 * @param buildSpec the array of build commands to run
	 * @see IProject#setDescription(IProjectDescription, int, IProgressMonitor)
	 * @see #getBuildSpec()
	 * @see #newCommand()
	 */
	public void setBuildSpec(ICommand[] buildSpec);

	/**
	 * Sets the comment for the described project.
	 * <p>
	 * Users must call {@link IProject#setDescription(IProjectDescription, int, IProgressMonitor)} 
	 * before changes made to this description take effect.
	 * </p>
	 *
	 * @param comment the comment for the described project
	 * @see IProject#setDescription(IProjectDescription, int, IProgressMonitor)
	 * @see #getComment()
	 */
	public void setComment(String comment);

	/**
	 * Sets the dynamic project references for the described project. 
	 * The projects need not exist in the workspace. Duplicates will be
	 * removed.  
	 * <p>
	 * Users must call {@link IProject#setDescription(IProjectDescription, int, IProgressMonitor)} 
	 * before changes made to this description take effect.
	 * </p>
	 * @see #getDynamicReferences()
	 * @see IProject#setDescription(IProjectDescription, int, IProgressMonitor)
	 * @param projects list of projects
	 * @since 3.0
	 */
	public void setDynamicReferences(IProject[] projects);

	/**
	 * Sets the local file system location for the described project.  The path must
	 * be either an absolute file system path, or a relative path whose first
	 * segment is the name of a defined workspace path variable.  If
	 * <code>null</code> is specified, the default location is used.
	 * <p>
	 * Setting the location on a description for a project which already
	 * exists has no effect; the new project location is ignored when the
	 * description is set on the already existing project. This method is 
	 * intended for use on descriptions for new projects or for destination 
	 * projects for <code>copy</code> and <code>move</code>.
	 * </p>
	 * <p>
	 * This operation maps the root folder of the project to the exact location
	 * provided.  For example, if the location for project named "P" is set
	 * to the path c:\my_plugins\Project1, the file resource at workspace path
	 * /P/index.html  would be stored in the local file system at 
	 * c:\my_plugins\Project1\index.html.
	 * </p>
	 *
	 * @param location the location for the described project or <code>null</code>
	 * @see #getLocation()
	 */
	public void setLocation(IPath location);

	/**
	 * Sets the location for the described project.  
	 * If <code>null</code> is specified, the default location is used.
	 * <p>
	 * Setting the location on a description for a project which already
	 * exists has no effect; the new project location is ignored when the
	 * description is set on the already existing project. This method is 
	 * intended for use on descriptions for new projects or for destination 
	 * projects for <code>copy</code> and <code>move</code>.
	 * </p>
	 * <p>
	 * This operation maps the root folder of the project to the exact location
	 * provided.  For example, if the location for project named "P" is set
	 * to the URI file://c:/my_plugins/Project1, the file resource at workspace path
	 * /P/index.html  would be stored in the local file system at 
	 * file://c:/my_plugins/Project1/index.html.
	 * </p>
	 *
	 * @param location the location for the described project or <code>null</code>
	 * @see #getLocationURI()
	 * @see IWorkspace#validateProjectLocationURI(IProject, URI)
	 * @since 3.2
	 */
	public void setLocationURI(URI location);

	/**
	 * Sets the name of the described project.
	 * <p>
	 * Setting the name on a description and then setting the 
	 * description on the project has no effect; the new name is ignored.
	 * </p>
	 * <p>
	 * Creating a new project with a description name which doesn't
	 * match the project handle name results in the description name
	 * being ignored; the project will be created using the name
	 * in the handle.
	 * </p>
	 *
	 * @param projectName the name of the described project
	 * @see IProject#setDescription(IProjectDescription, int, IProgressMonitor)
	 * @see #getName()
	 */
	public void setName(String projectName);

	/** 
	 * Sets the list of natures associated with the described project.
	 * A project created with this description will have these natures
	 * added to it in the given order.
	 * <p>
	 * Users must call {@link IProject#setDescription(IProjectDescription, int, IProgressMonitor)} 
	 * before changes made to this description take effect.
	 * </p>
	 *
	 * @param natures the list of natures
	 * @see IProject#setDescription(IProjectDescription, int, IProgressMonitor)
	 * @see #getNatureIds()
	 */
	public void setNatureIds(String[] natures);

	/**
	 * Sets the referenced projects, ignoring any duplicates.
	 * The order of projects is preserved.
	 * The projects need not exist in the workspace.
	 * <p>
	 * Users must call {@link IProject#setDescription(IProjectDescription, int, IProgressMonitor)} 
	 * before changes made to this description take effect.
	 * </p>
	 *
	 * @param projects a list of projects
	 * @see IProject#setDescription(IProjectDescription, int, IProgressMonitor)
	 * @see #getReferencedProjects()
	 */
	public void setReferencedProjects(IProject[] projects);
}
