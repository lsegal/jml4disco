package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues;

import java.util.Collection;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.RemoteProveVcServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.implementations.RemoteProveVcServerQueue;

public final class RemoteProveVcServerQueueFactory {

	private RemoteProveVcServerQueueFactory() {
		
	}
	
	public static final RemoteProveVcServerQueue newRemoteProveVcServerQueue(Collection<RemoteProveVcServer> servers) {
		RemoteProveVcServerQueue toReturn = new RemoteProveVcServerQueue(servers.size());
		for(RemoteProveVcServer s: servers) {
			toReturn.add(s);
		}
		return toReturn;
	}
	
}
