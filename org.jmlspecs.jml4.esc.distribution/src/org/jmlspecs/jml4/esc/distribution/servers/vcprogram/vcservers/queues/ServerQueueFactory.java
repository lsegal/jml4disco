/*
 * ServerQueueFactory
 * 
 * Version 2.0 
 *
 * January 28th, 2009
 * 
 * Contributors:
 * R Le Guen, N Grigoropoulos
 */
package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues;

import java.util.MissingResourceException;
import java.util.ResourceBundle;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.implementations.RemoteTomCatServer;

/**
 * This factory class will return an instance of SeverQueue. If no instance yet
 * has been created, it will create one and initialize it.
 */
public final class ServerQueueFactory {

	private static final String PROPERTIES_FILE = "dispatch"; // To initialize
																// the servers
	private static ServerQueue serverRegistry = null;

	private ServerQueueFactory() {

	}

	/**
	 * @return Will return an ServerQueue instance
	 */
	public static final ServerQueue getRemoteProveVcServerQueueInstance() {

		if (serverRegistry == null)
			serverRegistry = initServers();
		return serverRegistry;
	}

	/**
	 * This initializes the servers with the data from the configuration file
	 * 
	 * @return A new instance of RemoteProveVcServerQueue with the server data
	 *         initialized from the properties file.
	 */
	private static ServerQueue initServers() {
		try {
			ResourceBundle bundle = ResourceBundle.getBundle(PROPERTIES_FILE);

			// TODO check that numberOfServers key exists
			int numberOfServers = Integer.parseInt(bundle
					.getString("numberOfServers"));
			ServerQueue newRegistry = new ServerQueue(numberOfServers);

			for (int i = 1; i <= numberOfServers; i++) {
				newRegistry.add(new RemoteTomCatServer(bundle
						.getString("vcServer." + i)));
			}
			return newRegistry;
		} catch (MissingResourceException e) {
			e.printStackTrace();
		}
		return null;
	}
}
