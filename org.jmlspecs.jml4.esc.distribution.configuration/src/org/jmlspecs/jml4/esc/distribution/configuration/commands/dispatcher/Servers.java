package org.jmlspecs.jml4.esc.distribution.configuration.commands.dispatcher;

import java.util.List;

import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;
import org.jmlspecs.jml4.esc.distribution.configuration.FrontCommand;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.ServerMapper;

public class Servers extends FrontCommand {

	@Override
	public void execute(CommandInput arg) throws FrontControllerException {
		List<AbstractRemoteServer> servers = ServerMapper.findAll();
		arg.setAttribute("Servers", servers);
	}

}
