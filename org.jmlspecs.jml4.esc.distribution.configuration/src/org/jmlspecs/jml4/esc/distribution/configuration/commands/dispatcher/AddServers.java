package org.jmlspecs.jml4.esc.distribution.configuration.commands.dispatcher;

import org.jmlspecs.jml4.esc.distribution.configuration.FrontCommand;
import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;
import org.jmlspecs.jml4.esc.distribution.configuration.FrontControllerException;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerQueueRegistry;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerQueueRegistryException;

public class AddServers extends FrontCommand {

	@Override
	public void execute(CommandInput arg) throws FrontControllerException {
		String s = arg.getParameter("server-url");
		if(s!=null && !s.equals("")) {
			try {
				ServerQueueRegistry.addServer(s);
			} catch (ServerQueueRegistryException e) {
				throw new FrontControllerException(e);
			}
		}
		else {
			throw new FrontControllerException("No server-url parameters provided.");
		}
	}

	
	
}
