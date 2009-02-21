package org.jmlspecs.eclipse.jdt.ui.preferences;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.preferences.IWorkbenchPreferenceContainer;
import org.jmlspecs.eclipse.jdt.ui.Activator;



public class JmlPreferencePage extends PropertyAndPreferencePage {

	public static final String JML_PROPERTY_PAGE   = Activator.PLUGIN_ID + "jml_property_page_context"; //$NON-NLS-1$
	public static final String JML_PREFERENCE_PAGE = Activator.PLUGIN_ID + "jml_preference_page_context"; //$NON-NLS-1$
	
	public static final String PREF_ID= "org.jmlspecs.eclipse.jdt.ui.preferences.JmlPreferencePage"; //$NON-NLS-1$
	public static final String PROP_ID= "org.jmlspecs.eclipse.jdt.ui.properties.JmlPreferencePage"; //$NON-NLS-1$

	public static final String DATA_SELECT_OPTION_KEY= "select_option_key"; //$NON-NLS-1$
	public static final String DATA_SELECT_OPTION_QUALIFIER= "select_option_qualifier"; //$NON-NLS-1$
	
	private JmlConfigurationBlock fConfigurationBlock;
	
	public JmlPreferencePage() {
		setPreferenceStore(Activator.getDefault().getPreferenceStore());
		//setDescription(PreferencesMessages.getString("ProblemSeveritiesPreferencePage.description")); //$NON-NLS-1$
		
		// only used when page is shown programatically
		setTitle(PreferencesMessages.JmlPreferencePage_title);
	}
	
	/*
	 * @see org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createControl(Composite parent) {
		IWorkbenchPreferenceContainer container= (IWorkbenchPreferenceContainer) getContainer();
		fConfigurationBlock= new JmlConfigurationBlock(getNewStatusChangedListener(), getProject(), container);
		
		super.createControl(parent);
		if (isProjectPreferencePage()) {
			PlatformUI.getWorkbench().getHelpSystem().setHelp(getControl(), JML_PROPERTY_PAGE);
		} else {
			PlatformUI.getWorkbench().getHelpSystem().setHelp(getControl(), JML_PREFERENCE_PAGE);
		}
	}

	protected Control createPreferenceContent(Composite composite) {
		return fConfigurationBlock.createContents(composite);
	}
	
	protected boolean hasProjectSpecificOptions(IProject project) {
		return fConfigurationBlock.hasProjectSpecificOptions(project);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage#getPreferencePageID()
	 */
	protected String getPreferencePageID() {
		return PREF_ID;
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage#getPropertyPageID()
	 */
	protected String getPropertyPageID() {
		return PROP_ID;
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.DialogPage#dispose()
	 */
	public void dispose() {
		if (fConfigurationBlock != null) {
			fConfigurationBlock.dispose();
		}
		super.dispose();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage#enableProjectSpecificSettings(boolean)
	 */
	protected void enableProjectSpecificSettings(boolean useProjectSpecificSettings) {
		super.enableProjectSpecificSettings(useProjectSpecificSettings);
		if (fConfigurationBlock != null) {
			fConfigurationBlock.useProjectSpecificSettings(useProjectSpecificSettings);
		}
	}

	/*
	 * @see org.eclipse.jface.preference.IPreferencePage#performDefaults()
	 */
	protected void performDefaults() {
		super.performDefaults();
		if (fConfigurationBlock != null) {
			fConfigurationBlock.performDefaults();
		}
	}

	/*
	 * @see org.eclipse.jface.preference.IPreferencePage#performOk()
	 */
	public boolean performOk() {
	    if (fConfigurationBlock != null && !fConfigurationBlock.performOk()) {
			return false;
		}	
		return super.performOk();
	}
	
	/*
	 * @see org.eclipse.jface.preference.IPreferencePage#performApply()
	 */
	public void performApply() {
		if (fConfigurationBlock != null) {
			fConfigurationBlock.performApply();
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.PreferencePage#applyData(java.lang.Object)
	 */
	public void applyData(Object data) {
		super.applyData(data);
		if (data instanceof Map && fConfigurationBlock != null) {
			Map map= (Map) data;
			Object key= map.get(DATA_SELECT_OPTION_KEY);
			Object qualifier= map.get(DATA_SELECT_OPTION_QUALIFIER);
			if (key instanceof String && qualifier instanceof String) {
				fConfigurationBlock.selectOption((String) key, (String) qualifier);
			}
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage#setElement(org.eclipse.core.runtime.IAdaptable)
	 */
	public void setElement(IAdaptable element) {
		super.setElement(element);
		setDescription(null); // no description for property page
	}

}