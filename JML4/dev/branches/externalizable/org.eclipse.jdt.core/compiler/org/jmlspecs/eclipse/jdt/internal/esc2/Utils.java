/*
 * This file is part of a library of utilities for plugin projects.
 * Copyright 2004 David R. Cok
 * 
 * Created on Oct 6, 2004
 */
package org.jmlspecs.eclipse.jdt.internal.esc2;
// TODO FIXME - fix Log
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.nio.ByteBuffer;
import java.nio.charset.Charset;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

/**
 * This class contains a number of (static) utility methods for
 * use in plugins.
 * 
 * @author David R. Cok
 */

// FIXME - not sure that anything in here is being used

public class Utils {

	/** A convenience holder for the end-of-line String for the current platform. */
	final static public String eol = System.getProperty("line.separator"); // FIXME - is this right? //$NON-NLS-1$

	/**
	 * Adds the given nature to the given project, if it is not already added
	 * @param project The project to add the nature to
	 * @param natureId The nature to add
	 * @return true if the nature is added, false if the nature was already present
	 * @throws CoreException
	 */
	public static boolean addNature(IProject project, String natureId) throws CoreException {

		// if the project already has the nature, we return
		if(project.hasNature(natureId)) {
			return false;
		}
			
		// First we get the description object and then add the new nature ID to the project's 
		// description
		
		IProjectDescription description = project.getDescription();
		String[] ids = description.getNatureIds();
		String[] newIds = new String[ids.length + 1];
		System.arraycopy(ids, 0, newIds, 0, ids.length);
		newIds[ids.length] = natureId;
		description.setNatureIds(newIds);
		project.setDescription(description, null);
		return true;
	}

	/**
	 * Removes the given nature from the given project, if it is present
	 * @param project The project to remove the nature from
	 * @param natureId The nature to remove
	 * @return true if the nature was removed, false if the nature was not present
	 * @throws CoreException
	 */
	public static boolean removeNature(IProject project, String natureId) throws CoreException {
		IProjectDescription description = project.getDescription();
		String[] ids = description.getNatureIds();
		
		for(int i = 0; i < ids.length; ++i) {
			if(ids[i].equals(natureId)) {
				String[] newIds = new String[ids.length - 1];
				System.arraycopy(ids, 0, newIds, 0, i);
				System.arraycopy(ids, i + 1, newIds, i, ids.length - i - 1);
				description.setNatureIds(newIds);
				project.setDescription(description, null);
				return true;
			}
		}
		return false;
	}

	/* NOTE:
	 * Builders can be present in a project in either an enabled or
	 * disabled state.  I cannot find any API to switch between the
	 * two - in the UI, there is a toggle on the Builders page of the
	 * project preferences.  Consequently we muck with what I would
	 * presume is an internal representation in isDisabledCommand
	 * and newDisabledCommand.  The representation may well change;
	 * it also may not be robust for commands that have arguments.
	 * 
	 * I implemented these commands for four reasons: (a) to be able
	 * to add builders in the disabled state,  (b) to be able to
	 * provide menu and accelerator key mechanisms for a user to 
	 * turn builders on and off, (c) to be able to determine
	 * whether a builder was enabled or not, to give some feedback
	 * to the user, and (d) to avoid some bad behavior of disabled
	 * builders not being removed when a nature was removed.
	 * 
	 */
	/** This is the builder name used for disabled commands. */
	private static final String disabledBuilderName = "org.eclipse.ui.externaltools.ExternalToolBuilder";

	/** This is the attribute key used for disabled commands. */
	private static final String disabledBuilderKey = "LaunchConfigHandle";

	/**
	 * This routine checks whether the given command is an
	 * enabled instance of the given builder.
	 *  
	 * @param c The command to be tested
	 * @param b The builder
	 * @return true if the command is a enabled instance of the builder, false otherwise
	 */
	public static boolean isEnabledCommand(ICommand c, String b) {
		return c.getBuilderName().equals(b);
	}

	/**
	 * This routine checks whether the given command is a
	 * disabled instance of the given builder.  This may well
	 * be fragile with version changes.
	 * @param c The command to be tested
	 * @param b The builder
	 * @return true if the command is a disabled instance of the builder, false otherwise
	 */
	public static boolean isDisabledCommand(ICommand c, String b) {
		if (!c.getBuilderName().equals(disabledBuilderName)) return false;
		Map m = c.getArguments();
		Object v = m.get(disabledBuilderKey);
		if (v != null && (v instanceof String) &&
				((String)v).indexOf(b) != -1) return true;
		return false;
	}
	
	/**
	 * This method creates a new builder command of the specified type, but in
	 * a disabled state.  It is not valid if there already is a builder of this
	 * type present.
	 * 
	 * @param project 	   The project to which this will belong
	 * @param description  The project description
	 * @param builder      The builder name
	 * @return				the new builder command
	 * @throws CoreException
	 */
	public static ICommand newDisabledCommand(final IProject project, final IProjectDescription description, final String builder) throws CoreException {
		// Put this in a resource change environment
		final ICommand command = description.newCommand();
		ResourcesPlugin.getWorkspace().run(
				new IWorkspaceRunnable() {
					public void run(IProgressMonitor pm) throws CoreException {
						command.setBuilderName(disabledBuilderName);
						Map map = new HashMap();
						map.put(disabledBuilderKey,"<project>/.externalToolBuilders/"+builder+".launch");
						command.setArguments(map);
						IFolder dir = project.getFolder(".externalToolBuilders");
						if (!dir.exists()) dir.create(true,true,null);
						IFile f = dir.getFile(builder + ".launch");
						if (f.exists()) f.delete(true,false,null);
						String content = 
							"<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol +
							"<launchConfiguration type=\"org.eclipse.ant.AntBuilderLaunchConfigurationType\">" + eol +
							"<booleanAttribute key=\"org.eclipse.ui.externaltools.ATTR_BUILDER_ENABLED\" value=\"false\"/>" + eol +
							"<mapAttribute key=\"org.eclipse.ui.externaltools.ATTR_TOOL_ARGUMENTS\"/>" + eol +
							"<stringAttribute key=\"org.eclipse.ui.externaltools.ATTR_DISABLED_BUILDER\" value=\"" + builder + "\"/>" + eol +
							"</launchConfiguration>";
						ByteBuffer bb = Charset.forName("UTF-8").encode(content);
						f.create(new ByteArrayInputStream(bb.array(),bb.position(),bb.limit()-bb.position()),true,null);
					}
				}, null); // no progress monitor

		return command;
	}


	/**
	 * Adds the given builder to the list of commands.
	 * @param project   The project whose commands are being added to
	 * @param commands  The current set of project commands
	 * @param description The current project's description
	 * @param builder   The name of the builder to add, if not already present.
	 * @param enabled   If true, the builder is installed in the enabled state, if false
	 * 					it is installed in the disabled state
	 * @return			The resulting set of commands.
	 * @throws CoreException
	 */
	public static ICommand[] addBuilder(IProject project, ICommand[] commands, 
			IProjectDescription description, String builder, boolean enabled) throws CoreException {
		// If the builder is already specified as one of the build actions, do nothing
		
		for(int i = 0; i < commands.length; ++i) {
			ICommand c = commands[i];
			boolean isEnabled = isEnabledCommand(c,builder);
			if (isEnabled || isDisabledCommand(c,builder)) {
//				if (Log.on) Log.log("Builder " + builder + " already added to " + project.getName() + " : " +
//						(isEnabled ? "enabled" : "disabled"));
				return commands;
			}
		}
		
		// Otherwise, put the builder among the project's build actions
		
		ICommand command;
		if (enabled) {
			command = description.newCommand();
			command.setBuilderName(builder);
		} else {
			command = newDisabledCommand(project,description,builder);
		}
		ICommand[] newCommands = new ICommand[commands.length + 1];
		System.arraycopy(commands, 0, newCommands, 0, commands.length);
		newCommands[newCommands.length - 1] = command;
//		if (Log.on) Log.log("Builder " + builder + " added to " 
//				+ project.getName() +
//				(enabled?" enabled":" disabled"));
		return newCommands;
	}

	/**
	 * Adds an enabled builder to the given project
	 * @param project The project to add a builder to
	 * @param builder The builder to add
	 * @throws CoreException
	 */
	public static void addBuilder(IProject project, String builder) throws CoreException {
		IProjectDescription description = project.getDescription();
		ICommand[] commands = description.getBuildSpec();
		commands = addBuilder(project,commands,description,
				builder,
				true);
		description.setBuildSpec(commands);
		project.setDescription(description, null);
	}
	
	/**
	 * Removes the given builder from the list of commands.
	 * @param commands  The current set of project commands
	 * @param builder   The name of the builder to remove, if present.
	 * @return			The resulting set of commands.
	 */
	public static ICommand[] removeBuilder(ICommand[] commands, String builder) {
		// If any of the commands is the builder, remove it and return
		for (int i = 0; i < commands.length; ++i) {
			ICommand c = commands[i];
			boolean isEnabled = isEnabledCommand(c,builder);
			if (isEnabled || isDisabledCommand(c,builder)) {
				ICommand[] newCommands = new ICommand[commands.length - 1];
				System.arraycopy(commands, 0, newCommands, 0, i);
				System.arraycopy(commands, i + 1, newCommands, i, commands.length - i - 1);
				return newCommands;
			}
		}
		return commands;
	}

	/**
	 * Removes the given builder from a project.
	 * @param project   The project whose builder is to be removed
	 * @param builder   The name of the builder to remove, if present.
	 * @throws CoreException
	 */
	public static void removeBuilder(IProject project, String builder) throws CoreException {
		IProjectDescription description = project.getDescription();
		ICommand[] commands = description.getBuildSpec();
		commands = removeBuilder(commands,builder);
		description.setBuildSpec(commands);
		project.setDescription(description, null);
	}
	
//	/**
//	 * If the builder is not present in the commands list, no action occurs;
//	 * if it is present and disabled, it is enabled;
//	 * if it is present and enabled, no action occurs.
//	 * 
//	 * @param commands  The current set of project commands
//	 * @param description The description of the project
//	 * @param builder   The name of the builder to enable.
//	 * @return			The resulting set of commands.
//	 */
//	public ICommand[] enableBuilder(ICommand[] commands, 
//			IProjectDescription description, String builder) {
//		
//		for (int i = 0; i < commands.length; ++i) {
//			ICommand c = commands[i];
//			if (isEnabledCommand(c,builder)) return commands;
//			if (isDisabledCommand(c,builder)) {
//				ICommand command = description.newCommand();
//				command.setBuilderName(builder);
//				commands[i] = command;
//				return commands;
//			}
//		}
//		return commands;
//	}
//
//
//	/**
//	 * If the builder is not present in the commands list, no action occurs;
//	 * if it is present and disabled, no action occurs;
//	 * if it is present and enabled, it is disabled.
//	 * 
//	 * @param project   The project whose builder is being disabled
//	 * @param commands  The current set of project commands
//	 * @param description The description of the project
//	 * @param builder   The name of the builder to enable.
//	 * @return			The resulting set of commands.
//	 * @throws CoreException
//	 */
//	public static ICommand[] disableBuilder(IProject project, ICommand[] commands, 
//			IProjectDescription description, String builder) throws CoreException  {
//		
//		for (int i = 0; i < commands.length; ++i) {
//			ICommand c = commands[i];
//			if (isEnabledCommand(c,builder)) {
//				commands[i] = newDisabledCommand(project, description,builder);
//				return commands;
//			}
//			if (isDisabledCommand(c,builder)) return commands;
//		}
//		return commands;
//	}

	/**
	 * Checks whether a project is enabled for a given builder
	 * (both has the builder and the builder is turned on).
	 * @param p  The project to check
	 * @param builder The id of the builder to look for
	 * @return true if the project has the builder and it is enabled,
	 * 			false otherwise
	 * @throws CoreException
	 */
	public static boolean isBuilderEnabled(IProject p, String builder) throws CoreException {
		
		ICommand[] commands = p.getDescription().getBuildSpec();
		for (int i = 0; i < commands.length; ++i) {
			ICommand c = commands[i];
			if (isEnabledCommand(c,builder)) return true;
		}
		return false;
	}

	
	/**
	 * Converts a location (file system absolute path) into an IResource within
	 * the given project by searching the classpath for a source folder that
	 * contains the given location.  The problem is that source folders or files
	 * may be linked and consequently a location's absolute path does not tell
	 * what IResource it might be. 
	 * 
	 * @param project  The Java Project to look for a resource in
	 * @param location The absolute file system location to map into a resource
	 * @param onlyExported  FIXME
	 * @return  FIXME
	 */
//	public static IResource mapBack(IJavaProject project, String location, boolean onlyExported) {
//		try {
//			IClasspathEntry[] classPathEntries = project.getResolvedClasspath(false);
//			
//			for (int i = 0; i < classPathEntries.length; ++i) {
//				IClasspathEntry cpe = classPathEntries[i];
//				if (onlyExported && cpe.getEntryKind() != IClasspathEntry.CPE_SOURCE) continue;
//				IPath entry = cpe.getPath();
//				IResource res = getRoot().findMember(entry);
//				if (cpe.getEntryKind() == IClasspathEntry.CPE_LIBRARY) {
//					// Might be an internal or external library
//					// skip
//				} else if (cpe.getEntryKind() == IClasspathEntry.CPE_SOURCE) {
//					// The Eclipse documentation is a bit unclear or at odds with
//					// the actual behavior.  What I observe is that
//					// - FIXME what about a non-linked folder
//					// - a linked folder gives the same result for getLocation and getRawLocation
//					// - a project that is also a source folder gives null for getRawLocation
//					// Thus experiment would indicate that getLocation could always be used,
//					// but the documentation implies one could always use getRawLocation.  The following
//					// code is trying to be conservative. (NOTE)
//					if (res.isLinked()) {
//						String s = res.getRawLocation().toOSString();
//						if (location.startsWith(s)) {
//							IPath p = res.getFullPath().append(location.substring(s.length()));
//							IResource r = getRoot().findMember(p);
//							if (r != null) return r;
//						}
//					} // FIXME - what about non-linked?
//				} else if (cpe.getEntryKind() == IClasspathEntry.CPE_PROJECT) {
//					IResource s = mapBack(JavaCore.create((IProject)res),location,true);
//					if (s != null) return s;
//				} else {
////					Log.errorlog("Unexpected content kind as a classpath entry: " + cpe.getEntryKind(),null);
//				}
//			}
//		} catch (JavaModelException e) {
////			Log.errorlog("Unexpected failure to process the classpath: ",e);
//		}
//		return null;
//	}

	
	/**
	 * Returns the absolute file system location of a file inside a plugin.
	 * @param pluginName  The name of the plugin
	 * @param path  The path (as a String) of the file within the plugin
	 * @return The absolute file system location of the target file
	 * @throws IOException
	 */
	public static String findPluginResource(String pluginName, String path) throws IOException {
		// This is the 'official' way to find something that
		// is in the install location of the plugin, cf.
		// Official Eclipse Faq #103.
		// It is stated that this code will only work if the 
		// install location is on the local file system.
		Bundle bundle = Platform.getBundle(pluginName);
		
		IPath p = new Path(path);
		URL url = FileLocator.find(bundle, p, null);
		// The substring call is to remove an initial /
		// FIXME do we remove the / on all platforms?
		// FIXME - do we need to do these back-and-forth conversions of wil this do:
		// return Platform.resolve(url).getPath().substring(1);
		p = new Path(FileLocator.resolve(url).getPath()).makeAbsolute();
		String s = p.toOSString();
		if (System.getProperty("os.name").startsWith("Windows")) s = s.substring(1);  //$NON-NLS-1$//$NON-NLS-2$
		return s;
	}
	
	/**
	 * This method does what I think s.replaceAll("\\","\\\\")
	 * is supposed to do, but that crashes.
	 * @param s Input string
	 * @return the input string with any occurrence of a backslash
	 *    replaced by a double backslash
	 */
	public static String doubleBackslash(String s) {
		StringBuffer b = new StringBuffer();
		int n = s.length();
		int i = 0;
		int j = 0;
		while (i < n) {
			if (s.charAt(i) == '\\') {
				b.append(s.substring(j,i));
				b.append("\\\\"); //$NON-NLS-1$
				++i;
				j = i;
			} else {
				++i;
			}
		}
		b.append(s.substring(j,i));
		return b.toString();
	}

	

	/**
	 * Reads input from the input and writes it to the output until
	 * the input stream runs out of data, but does all this in a new thread.
	 * @param i Stream to read from
	 * @param o Stream to write to
	 */
	public static void readAllInput(final InputStream i, final OutputStream o) {
		(new Thread(){
			public void run() {
				try {
					int n;
					byte[] b = new byte[1000];
					while ((n=i.read(b)) != -1) {
						o.write(b,0,n);
					}
					o.flush();
					return;
				} catch (Exception e) {
					// FIXME - do something here???
					return;
				}
			}
		}).start();
	}

	public static int execAndWait(String[] args) throws IOException, InterruptedException {
		Process p = Runtime.getRuntime().exec(args);
//		Utils.readAllInput(new BufferedInputStream(p.getInputStream()),Log.logPrintStream());
//		Utils.readAllInput(new BufferedInputStream(p.getErrorStream()),Log.logPrintStream());									
		int z = p.waitFor();
		return z;
	}
	
	public static int execAndWait(String command, String[] env, File cd) throws IOException, InterruptedException {
		Process p = Runtime.getRuntime().exec(command,env,cd);
//		Utils.readAllInput(new BufferedInputStream(p.getInputStream()),Log.logPrintStream());
//		Utils.readAllInput(new BufferedInputStream(p.getErrorStream()),Log.logPrintStream());									
		int z = p.waitFor();
		return z;
	}
}
