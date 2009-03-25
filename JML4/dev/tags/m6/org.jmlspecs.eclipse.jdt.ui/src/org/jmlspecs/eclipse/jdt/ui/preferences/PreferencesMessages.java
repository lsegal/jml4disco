/*******************************************************************************
 * Copyright (c) 2000, 2007 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     John Kaplan, johnkaplantech@gmail.com - 108071 [code templates] template for body of newly created class
 *******************************************************************************/
package org.jmlspecs.eclipse.jdt.ui.preferences;

import org.eclipse.osgi.util.NLS;

public final class PreferencesMessages extends NLS {

	private static final String BUNDLE_NAME= "org.jmlspecs.eclipse.jdt.ui.preferences.PreferencesMessages";//$NON-NLS-1$

	private PreferencesMessages() {
		// Do not instantiate
	}

	public static String JmlPreferencePage_title;
	
	public static String JmlConfigurationBlock_common_description;
	
	public static String JmlConfigurationBlock_error;
	public static String JmlConfigurationBlock_warning;
	public static String JmlConfigurationBlock_ignore;
	
	public static String JmlConfigurationBlock_non_null;
	public static String JmlConfigurationBlock_nullable;
	
	public static String JmlGeneral_title;
	public static String JmlEnableJml_label;
	public static String JmlEnableJmlDbc_label;
	public static String JmlEnableJmlNewLoopSemantics_label;
	public static String JmlSpecPath_label;

	public static String JmlProgrammingSecifications_title;
	public static String JmlCommentDisabled_label;
	
	public static String JmlNonNullTypeSystem_title;
	public static String JmlNonNullTypeSystem_label;
	public static String JmlExplicitNullityAnnotation_label;
	public static String JmlDefaultNullity_label;
	public static String JmlSetJDTPotentialNPA_link;
	
	public static String JmlRac_title;
	public static String JmlEnableRac_label;
	public static String JmlEnableCounts_label;

	public static String JmlEsc_title;
	public static String JmlEnableJmlEsc_label;
	public static String JmlEsc2_common_description;
	public static String JmlEnableJmlEsc2_label;
	public static String JmlEsc2CommandLineArgs_label;
	public static String JmlEnableEsc2EchoOutput_label;
	
	public static String JmlSimplifyPath_label;
	
	public static String JmlFspv_title;
	public static String JmlEnableThy_label;
	
	public static String JmlTbd_label;
	
	public static String JmlConfigurationBlock_needsbuild_title;
	public static String JmlConfigurationBlock_needsfullbuild_message;
	public static String JmlConfigurationBlock_needsprojectbuild_message;
	
	public static String Jml2_title;
	public static String Jml2Enable_label;
	public static String Jml2EnableChecker_label;
	public static String Jml2EnableCompiler_label;
	
	public static String JmlDistributed_title;
	public static String JmlEnableDistributed_label;
	public static String JmlSpecPathDistributed_label;
	
	public static String JmlBoogie_title;
	public static String JmlEnableBoogie_label;
	
	static {
		NLS.initializeMessages(BUNDLE_NAME, PreferencesMessages.class);
	}
}
