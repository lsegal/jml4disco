package org.jmlspecs.jml4.esc.distribution.configuration.commands.dispatcher;

import org.jmlspecs.jml4.esc.distribution.configuration.FrontCommand;
import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerQueueRegistry;

public class RemoveServers extends FrontCommand {

	@Override
	public void execute(CommandInput arg) throws FrontControllerException {
		String s = arg.getParameter("server-name");
		if(s!=null && !s.equals("")) {
			ServerQueueRegistry.removeServer(s);
		}

		arg.setAttribute("servers", ServerQueueRegistry.getRemoteProveVcServerQueueInstance().toArray());
		
	}

	
	
}
