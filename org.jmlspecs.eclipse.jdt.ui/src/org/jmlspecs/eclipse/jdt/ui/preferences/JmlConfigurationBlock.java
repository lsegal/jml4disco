/*******************************************************************************
 * Copyright (c) 2000, 2006 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.jmlspecs.eclipse.jdt.ui.preferences;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.dialogs.StatusInfo;
import org.eclipse.jdt.internal.ui.preferences.OptionsConfigurationBlock;
import org.eclipse.jdt.internal.ui.preferences.ScrolledPageContent;
import org.eclipse.jdt.internal.ui.util.PixelConverter;
import org.eclipse.jdt.internal.ui.wizards.IStatusChangeListener;
import org.eclipse.jface.dialogs.ControlEnableState;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Link;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.PreferencesUtil;
import org.eclipse.ui.forms.widgets.ExpandableComposite;
import org.eclipse.ui.preferences.IWorkbenchPreferenceContainer;
/**
  */
public class JmlConfigurationBlock extends OptionsConfigurationBlock {

	private static final String SETTINGS_SECTION_NAME = "JmlConfigurationBlock";  //$NON-NLS-1$
	
	// Preference store keys, see JavaCore.getOptions
	
	private static final Key PREF_PB_NON_NULL_TYPE_SYSTEM = getJDTCoreKey(JavaCore.COMPILER_PB_NON_NULL_TYPE_SYSTEM);
	private static final Key PREF_EXPLICIT_NULLITY_ANNOTATION = getJDTCoreKey(JavaCore.COMPILER_EXPLICIT_NULLITY_ANNOTATION);
	private static final Key PREF_DEFAULT_NULLITY = getJDTCoreKey(JavaCore.COMPILER_DEFAULT_NULLITY);
	private static final Key PREF_ENABLE_RAC = getJDTCoreKey(JavaCore.COMPILER_ENABLE_RAC);
	private static final Key PREF_ENABLE_COUNTS = getJDTCoreKey(JavaCore.COMPILER_ENABLE_COUNTS);
	private static final Key PREF_SPEC_PATH = getJDTCoreKey(JavaCore.COMPILER_SPEC_PATH);
	private static final Key PREF_ENABLE_JML = getJDTCoreKey(JavaCore.COMPILER_ENABLE_JML);
	private static final Key PREF_ENABLE_JML_DBC = getJDTCoreKey(JavaCore.COMPILER_ENABLE_JML_DBC);
	private static final Key PREF_ENABLE_JML_NEW_LOOP_SEMANTICS = getJDTCoreKey(JavaCore.COMPILER_ENABLE_JML_NEW_LOOP_SEMANTICS);
	private static final Key PREF_ENABLE_JML_ESC2 = getJDTCoreKey(JavaCore.COMPILER_ENABLE_JML_ESC2);
	private static final Key PREF_ENABLE_ESC2_ECHO_OUTPUT = getJDTCoreKey(JavaCore.COMPILER_ENABLE_ESC2_ECHOOUTPUT);
	private static final Key PREF_ESC2_COMMANDLINE_ARGS = getJDTCoreKey(JavaCore.COMPILER_JML_ESC2_COMMANDLINEARGS);
	private static final Key PREF_ENABLE_JML_ESC = getJDTCoreKey(JavaCore.COMPILER_ENABLE_JML_ESC);
	private static final Key PREF_SIMPLIFY_PATH = getJDTCoreKey(JavaCore.COMPILER_SIMPLIFY_PATH);
	private static final Key PREF_ENABLE_JML_THY = getJDTCoreKey(JavaCore.COMPILER_ENABLE_JML_THY);
	private static final Key PREF_JML_COMMENTDISABLED = getJDTCoreKey(JavaCore.COMPILER_JML_COMMENTDISABLED);
	private static final Key PREF_ENABLE_JML2_CHECKER = getJDTCoreKey(JavaCore.COMPILER_ENABLE_JML2_CHECKER);
	private static final Key PREF_ENABLE_JML2_COMPILER = getJDTCoreKey(JavaCore.COMPILER_ENABLE_JML2_COMPILER);
	
	// values
	private static final String ERROR = JavaCore.ERROR;
	private static final String WARNING = JavaCore.WARNING;
	private static final String IGNORE = JavaCore.IGNORE;

	private static final String ENABLED = JavaCore.ENABLED;
	private static final String DISABLED = JavaCore.DISABLED;

	private static final String NON_NULL = JavaCore.NON_NULL;
	private static final String NULLABLE = JavaCore.NULLABLE;

	private PixelConverter fPixelConverter;
	
	private /*@nullable*/ Composite genComposite;
	private /*@nullable*/ Composite progProbsComposite;
	private /*@nullable*/ Composite nntComposite;
	private /*@nullable*/ Composite racComposite;
	private /*@nullable*/ Composite escComposite;
	private /*@nullable*/ Composite fspvComposite;
	private /*@nullable*/ Composite jml2Composite;

	private /*@nullable*/ ControlEnableState genEnableState;
	private /*@nullable*/ ControlEnableState progProbsEnableState;
	private /*@nullable*/ ControlEnableState nntEnableState;
	private /*@nullable*/ ControlEnableState racEnableState;
	private /*@nullable*/ ControlEnableState escCompositeState;
	private /*@nullable*/ ControlEnableState fspvCompositeState;
	private /*@nullable*/ ControlEnableState jml2ControlState;
	
	private Button jmlEnableButton;
	private Button jml2EnableCheckerCheckBox;
	private Button jml2EnableCompilerCheckBox;
	private Button esc4EnableCheckBox;
	private Button esc2EnableCheckBox;
	private Button fspvEnableCheckBox;
	
	public JmlConfigurationBlock(IStatusChangeListener context, IProject project, IWorkbenchPreferenceContainer container) {
		super(context, project, getKeys(), container);

// GK: No idea what this does but I do not believe we need it.		
//		// compatibilty code for the merge of the two option PB_SIGNAL_PARAMETER: 
//		if (ENABLED.equals(getValue(PREF_PB_SIGNAL_PARAMETER_IN_ABSTRACT))) {
//			setValue(PREF_PB_SIGNAL_PARAMETER_IN_OVERRIDING, ENABLED);
//		}
	}
	
	private static Key[] getKeys() {
		return new Key[] {
				PREF_PB_NON_NULL_TYPE_SYSTEM,
				PREF_EXPLICIT_NULLITY_ANNOTATION,
				PREF_DEFAULT_NULLITY,
				PREF_ENABLE_RAC,
				PREF_ENABLE_COUNTS,
				PREF_SPEC_PATH,
				PREF_ENABLE_JML,
				PREF_ENABLE_JML_DBC,
				PREF_ENABLE_JML_NEW_LOOP_SEMANTICS,
				PREF_ENABLE_JML_ESC2,
				PREF_ENABLE_JML_ESC,
				PREF_SIMPLIFY_PATH,
				PREF_ENABLE_JML_THY,
				PREF_JML_COMMENTDISABLED, 
				PREF_ENABLE_ESC2_ECHO_OUTPUT, 
				PREF_ESC2_COMMANDLINE_ARGS,
				PREF_ENABLE_JML2_CHECKER,
				PREF_ENABLE_JML2_COMPILER,
			};
	}
	
	/*
	 * @see org.eclipse.jface.preference.PreferencePage#createContents(Composite)
	 */
	protected Control createContents(Composite parent) {
		fPixelConverter = new PixelConverter(parent);
		setShell(parent.getShell());
		
		Composite mainComp = new Composite(parent, SWT.NONE);
		mainComp.setFont(parent.getFont());
		GridLayout layout = new GridLayout();
		layout.marginHeight = 0;
		layout.marginWidth = 0;
		mainComp.setLayout(layout);
		
		Composite commonComposite = createStyleTabContent(mainComp);
		GridData gridData = new GridData(GridData.FILL, GridData.FILL, true, true);
		gridData.heightHint = fPixelConverter.convertHeightInCharsToPixels(20);
		commonComposite.setLayoutData(gridData);
		
		validateSettings(null, null, null);
	
		return mainComp;
	}
	
	private Composite createStyleTabContent(Composite folder) {
		String[] errorWarningIgnore = new String[] { ERROR, WARNING, IGNORE };
		
		String[] errorWarningIgnoreLabels = new String[] {
			PreferencesMessages.JmlConfigurationBlock_error,  
			PreferencesMessages.JmlConfigurationBlock_warning, 
			PreferencesMessages.JmlConfigurationBlock_ignore
		};
		
		String[] nullableNonNull = new String[] { NULLABLE, NON_NULL };
		
		String[] nullableNonNullLabels = new String[] {
				PreferencesMessages.JmlConfigurationBlock_nullable,  
				PreferencesMessages.JmlConfigurationBlock_non_null
			};
		
		String[] enabledDisabled = new String[] { ENABLED, DISABLED };
		
		int nColumns = 3;
		
		final ScrolledPageContent sc1 = new ScrolledPageContent(folder);
		
		Composite composite = sc1.getBody();
		GridLayout layout = new GridLayout(nColumns, false);
		layout.marginHeight = 0;
		layout.marginWidth = 0;
		composite.setLayout(layout);

		Label description= new Label(composite, SWT.LEFT | SWT.WRAP);
		description.setFont(description.getFont());
		description.setText(PreferencesMessages.JmlConfigurationBlock_common_description); 
		description.setLayoutData(new GridData(GridData.BEGINNING, GridData.CENTER, true, false, nColumns - 1, 1));
				
		int indentStep = fPixelConverter.convertWidthInCharsToPixels(1);
		
		// int defaultIndent = indentStep * 0;
		int extraIndent = indentStep * 2;
		String label;
		ExpandableComposite excomposite;
		Composite inner;

		// enableJml
		label = PreferencesMessages.JmlEnableJml_label;
		jmlEnableButton = addCheckBox(composite, label, PREF_ENABLE_JML, enabledDisabled, 0);
		
		// General
		label = PreferencesMessages.JmlGeneral_title; 
		excomposite = createStyleSection(composite, label, nColumns);

		inner = new Composite(excomposite, SWT.NONE);
		genComposite = inner;
		inner.setFont(composite.getFont());
		inner.setLayout(new GridLayout(nColumns, false));
		excomposite.setClient(inner);
		// enableJmlDbc
		label = PreferencesMessages.JmlEnableJmlDbc_label;
		addCheckBox(inner, label, PREF_ENABLE_JML_DBC, enabledDisabled, extraIndent);
		// enableJmlNewLoopSemantics
		label = PreferencesMessages.JmlEnableJmlNewLoopSemantics_label;
		addCheckBox(inner, label, PREF_ENABLE_JML_NEW_LOOP_SEMANTICS, enabledDisabled, extraIndent);
		//specPath
		label = PreferencesMessages.JmlSpecPath_label;
		Text text = addTextField(inner, label, PREF_SPEC_PATH, extraIndent, 0);
		GridData gd = (GridData) text.getLayoutData();
		gd.widthHint = fPixelConverter.convertWidthInCharsToPixels(50);
		gd.horizontalAlignment= GridData.END;
		text.setTextLimit(255);
		
		Label inst = new Label(inner,SWT.LEFT);
        inst.setFont(description.getFont());
        inst.setText("(Use '${workspace}' or '${project}' "); 
        inst = new Label(inner,SWT.LEFT);
        inst.setFont(description.getFont());
        inst.setText("as appropriate in the spec path)"); 
		
        //Potential programming/specification problems
		label = PreferencesMessages.JmlProgrammingSecifications_title;
		excomposite = createStyleSection(composite, label, nColumns);
		
		inner = new Composite(excomposite, SWT.NONE);
		progProbsComposite = inner;
		inner.setFont(composite.getFont());
		inner.setLayout(new GridLayout(nColumns, false));
		excomposite.setClient(inner);
		//Possible inadvertent disabling of JML annotations
		label = PreferencesMessages.JmlCommentDisabled_label; 
		addComboBox(inner, label, PREF_JML_COMMENTDISABLED, errorWarningIgnore, errorWarningIgnoreLabels, extraIndent);
		
		// Non-Null Type System
		label = PreferencesMessages.JmlNonNullTypeSystem_title; 
		excomposite = createStyleSection(composite, label, nColumns);

		inner = new Composite(excomposite, SWT.NONE);
		nntComposite = inner;
		inner.setFont(composite.getFont());
		inner.setLayout(new GridLayout(nColumns, false));
		excomposite.setClient(inner);
		
		label = PreferencesMessages.JmlNonNullTypeSystem_label; 
		addComboBox(inner, label, PREF_PB_NON_NULL_TYPE_SYSTEM, errorWarningIgnore, errorWarningIgnoreLabels, extraIndent);		
		label = PreferencesMessages.JmlSetJDTPotentialNPA_link;
		addLink(inner, label, extraIndent);		
		label = PreferencesMessages.JmlDefaultNullity_label;
		addComboBox(inner, label, PREF_DEFAULT_NULLITY, nullableNonNull, nullableNonNullLabels, extraIndent);

		label = PreferencesMessages.JmlEnableCounts_label;
		addCheckBox(inner, label, PREF_ENABLE_COUNTS, enabledDisabled, extraIndent);
		label = PreferencesMessages.JmlExplicitNullityAnnotation_label;		
		addComboBox(inner, label, PREF_EXPLICIT_NULLITY_ANNOTATION, errorWarningIgnore, errorWarningIgnoreLabels, 4 * extraIndent);

		// RAC
		label = PreferencesMessages.JmlRac_title; 
		excomposite = createStyleSection(composite, label, nColumns);
		inner = new Composite(excomposite, SWT.NONE);
		racComposite = inner;
		inner.setFont(composite.getFont());
		inner.setLayout(new GridLayout(nColumns, false));
		excomposite.setClient(inner);

		label= PreferencesMessages.JmlEnableRac_label;
		addCheckBox(inner, label, PREF_ENABLE_RAC, enabledDisabled, extraIndent);

		// ESC
		label = PreferencesMessages.JmlEsc_title; 
		excomposite = createStyleSection(composite, label, nColumns);
		
		inner = new Composite(excomposite, SWT.NONE);
		escComposite = inner;
		inner.setFont(composite.getFont());
		inner.setLayout(new GridLayout(nColumns, false));
		excomposite.setClient(inner);
		// enableJmlEsc4
		label = PreferencesMessages.JmlEnableJmlEsc_label;
		esc4EnableCheckBox = addCheckBox(inner, label, PREF_ENABLE_JML_ESC, enabledDisabled, extraIndent);
		
		//ESC2
		Label escDescription = new Label(inner, SWT.LEFT | SWT.WRAP);
		escDescription.setFont(escDescription.getFont());
		escDescription.setText(PreferencesMessages.JmlEsc2_common_description); 
		escDescription.setLayoutData(new GridData(GridData.BEGINNING, GridData.CENTER, true, false, nColumns - 1, 2));
		// enableJmlEsc2
		label = PreferencesMessages.JmlEnableJmlEsc2_label;
		esc2EnableCheckBox = addCheckBox(inner, label, PREF_ENABLE_JML_ESC2, enabledDisabled, extraIndent);
		label = PreferencesMessages.JmlEnableEsc2EchoOutput_label;
		addCheckBox(inner, label, PREF_ENABLE_ESC2_ECHO_OUTPUT , enabledDisabled, extraIndent);
		label = PreferencesMessages.JmlEsc2CommandLineArgs_label;
		text = addTextField(inner, label, PREF_ESC2_COMMANDLINE_ARGS, extraIndent, 0);
		gd = (GridData) text.getLayoutData();
		gd.widthHint= fPixelConverter.convertWidthInCharsToPixels(50);
		gd.horizontalAlignment = GridData.END;
		text.setTextLimit(255);
		//simplifyPath
		label = PreferencesMessages.JmlSimplifyPath_label;
		text = addTextField(inner, label, PREF_SIMPLIFY_PATH, extraIndent, 0);
		gd = (GridData) text.getLayoutData();
		gd.widthHint = fPixelConverter.convertWidthInCharsToPixels(50);
		gd.horizontalAlignment = GridData.END;
		text.setTextLimit(255);

		// FSPV
		label = PreferencesMessages.JmlFspv_title; 
		excomposite = createStyleSection(composite, label, nColumns);

		inner = new Composite(excomposite, SWT.NONE);
		fspvComposite = inner;
		inner.setFont(composite.getFont());
		inner.setLayout(new GridLayout(nColumns, false));
		excomposite.setClient(inner);
		// enableLoop
		label = PreferencesMessages.JmlEnableThy_label;
		fspvEnableCheckBox = addCheckBox(inner, label, PREF_ENABLE_JML_THY, enabledDisabled, extraIndent);

		// JML2
		label = PreferencesMessages.Jml2_title; 
		excomposite = createStyleSection(composite, label, nColumns);

		inner = new Composite(excomposite, SWT.NONE);
		jml2Composite = inner;
		inner.setFont(composite.getFont());
		inner.setLayout(new GridLayout(nColumns, false));
		excomposite.setClient(inner);
		// enableJml2Checker
		//label=PreferencesMessages.Jml2Enable_label;
		//addCheckBox(inner, label, PREF_ENABLE_JML2, enabledDisabled, extraIndent);
		// enableJml2Checker
		label = PreferencesMessages.Jml2EnableChecker_label;
		jml2EnableCheckerCheckBox = addCheckBox(inner, label, PREF_ENABLE_JML2_CHECKER, enabledDisabled, extraIndent);
		// enableJml2Compiler
		label = PreferencesMessages.Jml2EnableCompiler_label;
		jml2EnableCompilerCheckBox = addCheckBox(inner, label, PREF_ENABLE_JML2_COMPILER, enabledDisabled, extraIndent);
		
		IDialogSettings section = JavaPlugin.getDefault().getDialogSettings().getSection(SETTINGS_SECTION_NAME);
		restoreSectionExpansionStates(section);
		
		return sc1;
	}
	
	/* (non-javadoc)
	 * Update fields and validate.
	 * @param changedKey Key that changed, or null, if all changed.
	 */	
	protected void validateSettings(/*@nullable*/Key changedKey, String oldValue, String newValue) {
		if (!areSettingsEnabled()) {
			return;
		}
//		if(changedKey != null &&
//			(PREF_ENABLE_JML.equals(changedKey)
//				|| PREF_ENABLE_JML2_CHECKER.equals(changedKey)
//				|| PREF_ENABLE_JML2_COMPILER.equals(changedKey)
//				|| PREF_ENABLE_JML_DBC.equals(changedKey))) {
//				updateEnableDisableStatusOfControls();
//		}
		updateEnableDisableStatusOfControls();
		fContext.statusChanged(new StatusInfo());
	}
	
	/*
	 * This adjusts the enabled/disabled status of some controls so that they
	 * appear grayed out or not based on the status of other controls.
	 */
	private void updateEnableDisableStatusOfControls() {
		boolean enableJml= checkValue(PREF_ENABLE_JML, ENABLED);
		boolean dbcEnabled = checkValue(PREF_ENABLE_JML_DBC, ENABLED);
		if (enableJml) {
			if (genEnableState != null) {
				genEnableState.restore();
				genEnableState = null;
			}
			if (progProbsEnableState!= null) {
				progProbsEnableState.restore();
				progProbsEnableState= null;
			}			
			if (nntEnableState != null) {
				nntEnableState.restore();
				nntEnableState = null;
			}
			if (racEnableState != null) {
				racEnableState.restore();
				racEnableState = null;
			}
			if (jml2ControlState == null) {
				jml2ControlState = ControlEnableState.disable(jml2Composite);
			}
		} else {
			if (genEnableState == null) {
				genEnableState = ControlEnableState.disable(genComposite);
			}
			if (nntEnableState == null) {
				nntEnableState = ControlEnableState.disable(nntComposite);
			}
			if (racEnableState == null) {
				racEnableState = ControlEnableState.disable(racComposite);
			}
			if (jml2ControlState != null) {
				jml2ControlState.restore();
				jml2ControlState = null;
			}
		}
		
		if (enableJml && dbcEnabled) {
			if (escCompositeState != null) {
				escCompositeState.restore();
				escCompositeState = null;
			}
			if (fspvCompositeState != null) {
				fspvCompositeState.restore();
				fspvCompositeState = null;
			}
		} else {
			if (escCompositeState == null) {
				escCompositeState = ControlEnableState.disable(escComposite);
			}
			if (fspvCompositeState == null) {
				fspvCompositeState = ControlEnableState.disable(fspvComposite);
			}
		}
	}

	protected String[] getFullBuildDialogStrings(boolean workspaceSettings) {
		String title = PreferencesMessages.JmlConfigurationBlock_needsbuild_title;
		String message;
		if (workspaceSettings) {
			message = PreferencesMessages.JmlConfigurationBlock_needsfullbuild_message; 
		} else {
			message = PreferencesMessages.JmlConfigurationBlock_needsprojectbuild_message; 
		}
		return new String[] { title, message };
	}

	public void dispose() {
		IDialogSettings section = JavaPlugin.getDefault().getDialogSettings().addNewSection(SETTINGS_SECTION_NAME);
		storeSectionExpansionStates(section);
		super.dispose();
	}

	private void addLink(Composite composite, String text, int indent) {
		GridData gd;
		final Link link = new Link(composite, SWT.NONE);
		link.setText(text);
		gd = new GridData(SWT.FILL, SWT.BEGINNING, true, false);
		gd.widthHint = 300; // don't get wider initially
		gd.horizontalSpan = 2;
		gd.horizontalIndent = indent;
		link.setLayoutData(gd);
		link.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				PreferencesUtil.createPreferenceDialogOn(link.getShell(), e.text, null, null);
			}
		});
	}	
	
}
