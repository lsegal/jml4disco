package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues;

public class ServerQueueRegistryException extends Exception {

	public ServerQueueRegistryException() {
		super();
	}
	
	public ServerQueueRegistryException(String s) {
		super(s);
	}

	public ServerQueueRegistryException(Exception e) {
		super(e);
	}
	
	public ServerQueueRegistryException(String s, Exception e) {
		super(s, e);
	}
	
}
