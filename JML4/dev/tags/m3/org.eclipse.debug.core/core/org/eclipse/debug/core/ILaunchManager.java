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
package org.eclipse.debug.core;

 
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IPersistableSourceLocator;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.sourcelookup.ISourceContainerType;
import org.eclipse.debug.core.sourcelookup.ISourcePathComputer;

/**
 * The launch manager manages the set of registered launches, maintaining
 * a collection of active processes and debug targets. Clients interested
 * in launch notification may register with the launch manager.
 * @see ILaunch
 * @see ILaunchListener
 * @noimplement This interface is not intended to be implemented by clients.
 */
public interface ILaunchManager {
	/**
	 * A launch in a normal, non-debug mode(value <code>"run"</code>).
	 */
	public static final String RUN_MODE= "run"; //$NON-NLS-1$
	/**
	 * A launch in a special debug mode (value <code>"debug"</code>).
	 */
	public static final String DEBUG_MODE= "debug"; //$NON-NLS-1$
	/**
	 * A launch in a special profile mode (value <code>"profile"</code>).
	 * @since 3.0
	 */
	public static final String PROFILE_MODE= "profile"; //$NON-NLS-1$	
	
	/**
	 * Launch configuration attribute name. The value is a map of environment
	 * variables passed into Runtime.exec(...) when a launch configuration is launched.
	 * Default value is <code>null</code> which indicates the default environment
	 * should be used. 
	 * 
	 * @since 3.0
	 */
	public static final String ATTR_ENVIRONMENT_VARIABLES = DebugPlugin.getUniqueIdentifier() + ".environmentVariables"; //$NON-NLS-1$
	
	/**
	 * Launch configuration attribute name. The value is a boolean value specifying
	 * whether the environment variables in a launch configuration
	 * should be appended to the native environment (i.e. when <code>true</code>),
	 * or if they should replace the environment (i.e. <code>false</code>). The
	 * default value is <code>true</code>.
	 * 
	 * @since 3.0 
	 */
	public static final String ATTR_APPEND_ENVIRONMENT_VARIABLES = DebugPlugin.getUniqueIdentifier() + ".appendEnvironmentVariables"; //$NON-NLS-1$	
	
	/**
	 * Adds the specified launch and notifies listeners. Has no
	 * effect if an identical launch is already registered.
	 * 
	 * @param launch the launch to add
	 * @since 2.0
	 */
	public void addLaunch(ILaunch launch);
	/**
	 * Adds the given launch configuration listener to the list
	 * of listeners notified when a launch configuration is
	 * added, removed, or changed. Has no effect if the given listener
	 * is already registered.
	 * 
	 * @param listener launch configuration listener
	 * @since 2.0
	 */
	public void addLaunchConfigurationListener(ILaunchConfigurationListener listener);	
	/**
	 * Adds the specified launch objects and notifies listeners. Has no
	 * effect on identical launch objects already registered.
	 * 
	 * @param launches the launch objects to add
	 * @since 2.1
	 */
	public void addLaunches(ILaunch[] launches);	
	/**
	 * Adds the given listener to the collection of registered launch listeners.
	 * Has no effect if an identical listener is already registered.
	 *
	 * @param listener the listener to register
	 * @since 2.1
	 */
	public void addLaunchListener(ILaunchesListener listener);		
	/**
	 * Adds the given listener to the collection of registered launch listeners.
	 * Has no effect if an identical listener is already registered.
	 *
	 * @param listener the listener to register
	 */
	public void addLaunchListener(ILaunchListener listener);
	/**
	 * Return a String that can be used as the name of a launch configuration.  The name
	 * is guaranteed to be unique (no existing launch configurations will have this name).
	 * The name that is returned uses the <code>namePrefix</code> as a starting point.  If 
	 * there is no existing launch configuration with this name, then <code>namePrefix</code>
	 * is returned.  Otherwise, the value returned consists of the specified prefix plus
	 * some suffix that guarantees uniqueness.
	 * 
	 * @param namePrefix the String that the returned name must begin with
	 * @return launch configuration name
	 * @since 2.0
	 */
	public String generateUniqueLaunchConfigurationNameFrom(String namePrefix);
	/**
	 * Returns the collection of debug targets currently registered with this
	 * launch manager.
	 *
	 * @return an array of debug targets
	 */
	public IDebugTarget[] getDebugTargets();
	/** 
	 * Returns an array of environment variables to be used when
	 * launching the given configuration or <code>null</code> if unspecified.
	 * Each entry is of the form "<code>var_name=value</code>".
	 * 
	 * @return an array of environment variables to use when launching the given
	 *  configuration or <code>null</code> if unspecified
	 * @param configuration launch configuration
	 * @throws CoreException if unable to access associated attribute or if
	 * unable to resolve a variable in an environment variable's value
	 * @since 3.0
	 */
	public String[] getEnvironment(ILaunchConfiguration configuration) throws CoreException;
	/**
	 * This method returns the character encoding to use when launching the specified <code>ILaunchConfiguration</code>.
	 * The returned encoding can be derived from one of three places in the following order:
	 * <ol> 
	 * <li>An attribute saved on the configuration itself (where no attribute means use the default encoding).</li>
	 * <li>The mapped resources for the configuration, in the event one of them has a specific encoding that 
	 * is not the workspace default. If there are more than one mapped resource we optimistically ask only the first resource
	 * for its encoding.</li>
	 * <li>We ask the <code>ResourcesPlugin</code> for the workspace preference (which resolves back to the system
	 * property <code>file.encoding</code> if the user has made no changes to the workspace encoding preference).</li>
	 * </ol>
	 * @param configuration the <code>ILaunchConfiguration</code> to get the encoding for
	 * @return the encoding to use when launching the specified <code>ILaunchConfiguration</code>
	 * @throws CoreException
	 * 
	 * @since 3.4
	 */
	public String getEncoding(ILaunchConfiguration configuration) throws CoreException;
	/**
	 * Returns a handle to the launch configuration contained
	 * in the specified file. This method does not check if the specified <code>IFile</code> is 
	 * a launch configuration file or that it exists in the local or
	 * remote file system.
	 * 
	 * @param file launch configuration file
	 * @return a handle to the launch configuration contained
	 *  in the specified file
	 * @since 2.0
	 */
	public ILaunchConfiguration getLaunchConfiguration(IFile file);		
	/**
	 * Returns a handle to the launch configuration specified by
	 * the given memento. The configuration may not exist.
	 * 
	 * @param memento launch configuration memento
	 * @return a handle to the launch configuration specified by
	 *  the given memento
	 * @exception CoreException if the given memento is invalid or
	 *  an exception occurs parsing the memento
	 * @see ILaunchConfiguration#getMemento()
	 * @since 2.0
	 */
	public ILaunchConfiguration getLaunchConfiguration(String memento) throws CoreException;
	/**
	 * Returns all launch configurations defined in the workspace.
	 * 
	 * @return all launch configurations defined in the workspace
	 * @exception CoreException if an exception occurs retrieving configurations
	 * @since 2.0
	 */
	public ILaunchConfiguration[] getLaunchConfigurations() throws CoreException;	
	/**
	 * Returns all launch configurations of the specified type defined in the workspace
	 * 
	 * @param type a launch configuration type
	 * @return all launch configurations of the specified type defined in the workspace
	 * @exception CoreException if an error occurs while retrieving
	 *  a launch configuration
	 * @since 2.0
	 */
	public ILaunchConfiguration[] getLaunchConfigurations(ILaunchConfigurationType type) throws CoreException;
	
	/**
	 * Returns the launch configuration type extension with the specified
	 * id, or <code>null</code> if it does not exist.
	 * 
	 * @param id unique identifier for a launch configuration type extension
	 * @return the launch configuration type extension with the specified
	 * id, or <code>null</code> if it does not exist
	 * @since 2.0
	 */
	public ILaunchConfigurationType getLaunchConfigurationType(String id);
	
	/**
	 * Returns all defined launch configuration type extensions
	 * 
	 * @return all defined launch configuration type extensions
	 * @since 2.0
	 */
	public ILaunchConfigurationType[] getLaunchConfigurationTypes();
	
	/**
	 * Returns the collection of launches currently registered
	 * with this launch manager.
	 * 
	 * @return an array of launches
	 */
	public ILaunch[] getLaunches();
	
	/**
	 * Returns the launch mode registered with the given mode identifier,
	 * or <code>null</code> if none.
	 * 
	 * @param mode mode identifier
	 * @return launch mode or <code>null</code>
	 * @since 3.0
	 */
	public ILaunchMode getLaunchMode(String mode);
	
	/**
	 * Returns all registered launch modes.
	 * 
	 * @return all registered launch modes
	 * @since 3.0
	 */
	public ILaunchMode[] getLaunchModes();
	
	/**
	 * Returns a collection of launch configurations that required migration to be
	 * compatible with current tooling.
	 * 
	 * @return a collection of launch configurations that required migration
	 * @exception org.eclipse.core.runtime.CoreException if an exception occurs determining
	 * 	 migration candidates
	 * @since 3.2
	 */
	public ILaunchConfiguration[] getMigrationCandidates() throws CoreException;
	
	/**
	 * When a launch configuration is created or moved, registered launch
	 * configuration listeners (see <code>ILaunchConfigurationListener</code>)
	 * are notified of an add notification for the new configuration. If the
	 * notification is the result of a move this method will return a handle to
	 * the launch configuration that the added launch configuration was moved
	 * from. This method returns <code>null</code> if the added launch
	 * configuration was not the result of a rename or move. This information is
	 * only available during the add notification call back
	 * <code>launchConfigurationAdded</code>.
	 * <p>
	 * Renaming a configuration is considered the same as moving a
	 * configuration.
	 * </p>
	 * 
	 * @param addedConfiguration a launch configuration for which an add
	 * notification is being broadcast
	 * @return the launch configuration that the added launch configuration was
	 * moved from, or <code>null</code> if the add notification is not the
	 * result of a move
	 * @since 2.1
	 */
	public ILaunchConfiguration getMovedFrom(ILaunchConfiguration addedConfiguration);
	
	/**
	 * When a launch configuration is deleted or moved, registered launch
	 * configuration listeners (see <code>ILaunchConfigurationListener</code>)
	 * are notified of a remove notification for launch configuration that has
	 * been deleted. If the notification is the result of a move this method
	 * will return a handle to the launch configuration that the removed launch
	 * configuration was moved to. This method returns <code>null</code> if the
	 * removed launch configuration was not the result of a rename or move. This
	 * information is only available during the add notification call back
	 * <code>launchConfigurationRemoved</code>.
	 * <p>
	 * Renaming a configuration is considered the same as moving a
	 * configuration.
	 * </p>
	 *
	 * @param removedConfiguration a launch configuration for which a
	 * remove notification is being broadcast
	 * @return the launch configuration that the removed launch configuration
	 * was moved to, or <code>null</code> if the add notification is not the
	 * result of a move
	 * @since 2.1
	 */
	public ILaunchConfiguration getMovedTo(ILaunchConfiguration removedConfiguration);	
	
	/**
	 * Returns the native system environment variables as a map of
	 * variable names and values (Strings).
	 * <p>
	 * Note that WIN32 system environment preserves
	 * the case of variable names but is otherwise case insensitive.
	 * Depending on what you intend to do with the environment, the
	 * lack of normalization may or may not be create problems. On 
	 * WIN32, this method normalizes mixed-case keys variable names
	 * to upper case. Use {@link #getNativeEnvironmentCasePreserved()}
	 * instead to get a WIN32 system environment where the keys are
	 * the mixed-case variable names recorded by the OS.
	 * </p>
	 * 
	 * @return the native system environment variables; on WIN32, mixed-case
	 * variable names (keys) have been normalized to upper case
	 * (key type: <code>String</code>; value type: <code>String</code>)
	 * @since 3.0
	 */	
	public Map getNativeEnvironment();

	/**
	 * Returns the native system environment variables as a map of
	 * variable names and values (Strings).
	 * <p>
	 * Note that WIN32 system environment preserves
	 * the case of variable names but is otherwise case insensitive.
	 * Depending on what you intend to do with the environment, the
	 * lack of normalization may or may not be create problems. This
	 * method returns mixed-case keys using the variable names 
	 * recorded by the OS.
	 * Use {@link #getNativeEnvironment()} instead to get a WIN32 system
	 * environment where all keys have been normalized to upper case.
	 * </p>
	 * 
	 * @return the native system environment variables; on WIN32, mixed-case
	 * variable names (keys) are returned without normalization
	 * (key type: <code>String</code>; value type: <code>String</code>)
	 * @since 3.1
	 */	
	public Map getNativeEnvironmentCasePreserved();

	/**
	 * Returns the collection of processes currently registered with this
	 * launch manager.
	 *
	 * @return an array of processes
	 */
	public IProcess[] getProcesses();
	
	/**
	 * Returns the source container type extension registered with the
	 * given unique identifier, or <code>null</code> if none.
	 * 
	 * @param id unique identifier of a source container type extension
	 * @return the source container type extension registered with the
	 * given unique identifier, or <code>null</code> if none
	 * @since 3.0
	 */
	public ISourceContainerType getSourceContainerType(String id);
	
	/**
	 * Returns all registered source container type extensions.
	 * 
	 * @return all registered source container type extensions
	 * @since 3.0
	 */
	public ISourceContainerType[] getSourceContainerTypes();

	/**
	 * Returns a source path computer to compute a default source lookup path for
	 * the given launch configuration, or <code>null</code> if a source path
	 * computer has not been registered for the associated launch configuration
	 * type.
	 *  
	 * @param configuration a launch configuration
	 * @return a source path computer registered for the associated launch
	 *  configurations type, or <code>null</code> if unspecified
	 * @throws CoreException if an exception occurs while instantiating a source
	 *  path computer
	 * @since 3.0
	 */
	public ISourcePathComputer getSourcePathComputer(ILaunchConfiguration configuration) throws CoreException;
	
	/**
	 * Returns the source path computer extension registered with the given
	 * unique identifier, or <code>null</code> if none.
	 * 
	 * @param id source path computer identifier
	 * @return the source path computer extension registered with the given
	 * unique identifier, or <code>null</code> if none
	 * @since 3.0
	 */
	public ISourcePathComputer getSourcePathComputer(String id);	
	
	/**
	 * Return <code>true</code> if there is a launch configuration with the specified name, 
	 * <code>false</code> otherwise.
	 * 
	 * @return whether a launch configuration already exists with the given name
	 * @param name the name of the launch configuration whose existence is being checked
	 * @exception CoreException if unable to retrieve existing launch configuration names
	 * @since 2.0
	 */
	public boolean isExistingLaunchConfigurationName(String name) throws CoreException;
	
	/**
	 * Returns whether the given launch is currently registered.
	 * 
	 * @param launch a launch
	 * @return whether the launch is currently registered
	 * @since 3.1
	 */
	public boolean isRegistered(ILaunch launch);
	
	/**
	 * Creates and returns a new source locator of the specified
	 * type.
	 * 
	 * @param identifier the identifier associated with a 
	 *  persistable source locator extension
	 * @return a source locator
	 * @exception CoreException if an exception occurs creating
	 *  the source locator
	 * @since 2.0
	 */
	public IPersistableSourceLocator newSourceLocator(String identifier) throws CoreException;

	/**
	 * Removes the specified launch and notifies listeners.
	 * Has no effect if an identical launch is not already
	 * registered.
	 *
	 * @param launch the launch to remove
	 * @since 2.0
	 */
	public void removeLaunch(ILaunch launch);

	/**
	 * Removes the given launch configuration listener from the list
	 * of listeners notified when a launch configuration is
	 * added, removed, or changed. Has no effect if the given listener
	 * is not already registered.
	 * 
	 * @param listener launch configuration listener
	 * @since 2.0
	 */
	public void removeLaunchConfigurationListener(ILaunchConfigurationListener listener);

	/**
	 * Removes the specified launch objects and notifies listeners.
	 * Has no effect on identical launch objects that are not already
	 * registered.
	 *
	 * @param launches the launch objects to remove
	 * @since 2.1
	 */
	public void removeLaunches(ILaunch[] launches);
	
	/**
	 * Removes the given listener from the collection of registered launch listeners.
	 * Has no effect if an identical listener is not already registered.
	 *
	 * @param listener the listener to unregister
	 * @since 2.1
	 */
	public void removeLaunchListener(ILaunchesListener listener);
	
	/**
	 * Removes the given listener from the collection of registered launch listeners.
	 * Has no effect if an identical listener is not already registered.
	 *
	 * @param listener the listener to unregister
	 */
	public void removeLaunchListener(ILaunchListener listener);
	
}


