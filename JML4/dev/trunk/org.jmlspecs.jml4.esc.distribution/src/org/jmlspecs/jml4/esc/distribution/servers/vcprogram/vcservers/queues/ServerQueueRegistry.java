package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues;

import java.net.MalformedURLException;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.implementations.RemoteTomCatServer;

/**
 * This factory class will return an instance of SeverQueue. If no instance yet
 * has been created, it will create one and initialize it.
 */
public final class ServerQueueRegistry {

	private static final String PROPERTIES_FILE = "jml4-disco-dispatcher"; // To initialize
																// the servers
	private static ServerQueue serverqueue = null;

	private ServerQueueRegistry() {

	}

	/**
	 * @return Will return an ServerQueue instance
	 */
	public static final ServerQueue getRemoteProveVcServerQueueInstance() {

		if (serverqueue == null)
			serverqueue = initServers();
		return serverqueue;
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
			ServerQueue newqueue = new ServerQueue(numberOfServers);

			for (int i = 1; i <= numberOfServers; i++) {
				String serverInfo = bundle.getString("proverServer." + i);
				try {
					newqueue.add(new RemoteTomCatServer(serverInfo));
				}
				catch(MalformedURLException e) {
					System.out.println("Unable to add server '"+serverInfo+"'");
					e.printStackTrace();
				}
			}
			return newqueue;
		} catch (MissingResourceException e) {
			e.printStackTrace();
		}
		return null;
	}
	
	public static void addServer(String serverInfo) throws ServerQueueRegistryException {
		try {
			getRemoteProveVcServerQueueInstance().add(new RemoteTomCatServer(serverInfo));
		} catch (MalformedURLException e) {
			throw new ServerQueueRegistryException("Unable to add server '"+serverInfo+"'", e);
		}
	}
}
