package org.jmlspecs.jml4.esc.distribution.configuration.commands.dispatcher;

import java.io.IOException;

import org.jmlspecs.jml4.esc.distribution.configuration.FrontCommand;
import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerQueueRegistry;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.technicalservices.RemoteServersMapper;

public class RemoveServers extends FrontCommand {

	@Override
	public void execute(CommandInput arg) throws FrontControllerException {
		String s = arg.getParameter("server-name");
		if(s!=null && !s.equals("")) {
			AbstractRemoteServer server;
			try {
				server = RemoteServersMapper.findByUniqueName(s);
				if(server!=null) {
					RemoteServersMapper.destroy(server);
					arg.setAttribute("out", "Server removed successfully");
				}
			} catch (IOException e) {
				throw new FrontControllerException(e);
			} 
		}

		arg.setAttribute("servers", ServerQueueRegistry.getRemoteProveVcServerQueueInstance().toArray());
		
	}

	
	
}
