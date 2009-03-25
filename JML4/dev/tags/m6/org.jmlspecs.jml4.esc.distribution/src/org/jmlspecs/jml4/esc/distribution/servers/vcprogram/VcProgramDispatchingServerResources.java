package org.jmlspecs.jml4.esc.distribution.servers.vcprogram;

import java.util.ResourceBundle;

public class VcProgramDispatchingServerResources {

	private static final String PROPERTIES_FILE = "jml4-disco-dispatcher"; // To initialize
	private static final ResourceBundle bundle = ResourceBundle.getBundle(PROPERTIES_FILE);
	
	public static String getProperty(String name) {
		return bundle.getString(name);
	}
	
}
