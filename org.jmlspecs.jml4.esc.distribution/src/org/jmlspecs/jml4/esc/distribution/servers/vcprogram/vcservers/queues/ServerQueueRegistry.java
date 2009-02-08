package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues;

import java.net.MalformedURLException;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.ServerMapper;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.implementations.RemoteTomCatServer;

/**
 * This factory class will return an instance of SeverQueue. If no instance yet
 * has been created, it will create one and initialize it.
 */
public final class ServerQueueRegistry {
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
		ServerQueue newqueue = new ServerQueue(ServerMapper.findAll());

		return newqueue;
	}

	public static void addServer(String serverInfo) throws ServerQueueRegistryException {
		try {
			getRemoteProveVcServerQueueInstance().add(new RemoteTomCatServer(serverInfo));
		} catch (MalformedURLException e) {
			throw new ServerQueueRegistryException("Unable to add server '"+serverInfo+"'", e);
		}
	}
}
