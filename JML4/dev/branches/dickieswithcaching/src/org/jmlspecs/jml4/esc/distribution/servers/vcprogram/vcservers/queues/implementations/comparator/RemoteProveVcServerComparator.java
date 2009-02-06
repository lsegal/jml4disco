package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.implementations.comparator;

import java.util.Comparator;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.RemoteProveVcServer;

public class RemoteProveVcServerComparator implements Comparator<RemoteProveVcServer> {

	public int compare(RemoteProveVcServer arg0, RemoteProveVcServer arg1) {
		//return (int)(((double)arg1.getPendingVcs()/arg1.getSystemLoadAverage())-((double)arg0.getPendingVcs()/arg0.getSystemLoadAverage()));
		return (int)((double)(arg0.getPendingVcs()*100)/arg0.getSystemLoadAverage())-(int)((double)(arg1.getPendingVcs()*100)/arg1.getSystemLoadAverage());
	}
	
}
