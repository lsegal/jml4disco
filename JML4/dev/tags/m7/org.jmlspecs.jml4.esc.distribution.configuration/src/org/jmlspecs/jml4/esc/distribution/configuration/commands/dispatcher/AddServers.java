package org.jmlspecs.jml4.esc.distribution.configuration.commands.dispatcher;

import java.io.IOException;
import java.net.MalformedURLException;

import org.jmlspecs.jml4.esc.distribution.configuration.FrontCommand;
import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.implementations.RemoteTomCatServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.technicalservices.RemoteServersMapper;

public class AddServers extends FrontCommand {

	@Override
	public void execute(CommandInput arg) throws FrontControllerException {
		String s = arg.getParameter("server-url");
		if(s!=null && !s.equals("")) {
			try {
				RemoteTomCatServer server = new RemoteTomCatServer(s);
				RemoteServersMapper.insert(server);
				arg.setAttribute("out", "Server added successfully");
			} catch (MalformedURLException e) {
				throw new FrontControllerException(e);
			} catch (IOException e) {
				throw new FrontControllerException(e);
			}
		}
	}

	
	
}
