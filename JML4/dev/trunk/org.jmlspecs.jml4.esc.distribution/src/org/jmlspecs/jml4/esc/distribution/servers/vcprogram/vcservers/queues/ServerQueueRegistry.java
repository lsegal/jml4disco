package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.technicalservices.RemoteServersMapper;

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
		
		try {
			AbstractRemoteServer[] servers = RemoteServersMapper.findAll();
	
			ServerQueue newqueue = new ServerQueue(servers.length);
			
			for (int i = 0; i < servers.length; i++) {
				newqueue.add(servers[i]);
			}
			return newqueue;
		}
		catch(Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	public static void addServer(AbstractRemoteServer prover) throws ServerQueueRegistryException {
		try {
			getRemoteProveVcServerQueueInstance().add(prover);
			System.out.println("added?");
		} catch (Exception e) {
			throw new ServerQueueRegistryException("Unable to add server '"+prover.toString()+"'", e);
		}
	}

	public static void removeServer(AbstractRemoteServer prover) {
		for(Object s:getRemoteProveVcServerQueueInstance().toArray()) {
			if(prover.toString().equals(s.toString())) {
				getRemoteProveVcServerQueueInstance().remove(s);
				System.out.println("removed?");
				return;
			}
		}
	}
}
