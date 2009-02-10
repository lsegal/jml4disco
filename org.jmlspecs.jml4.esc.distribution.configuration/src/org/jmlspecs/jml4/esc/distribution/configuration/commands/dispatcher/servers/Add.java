package org.jmlspecs.jml4.esc.distribution.configuration.commands.dispatcher.servers;

import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;
import org.jmlspecs.jml4.esc.distribution.configuration.commands.dispatcher.Servers;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerRegistry;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerQueueRegistryException;

public class Add extends Servers {

	@Override
	public void execute(CommandInput arg) throws FrontControllerException {
		String s = arg.getParameter("server-url");
		if(s!=null && !s.equals("")) {
			try {
				ServerRegistry.newServer(s);
			} catch (ServerQueueRegistryException e) {
				throw new FrontControllerException(e);
			}
			super.execute(arg);
		}
		else {
			super.execute(arg);
			throw new FrontControllerException("No server-url parameters provided.");
		}
	}

	
	
}
