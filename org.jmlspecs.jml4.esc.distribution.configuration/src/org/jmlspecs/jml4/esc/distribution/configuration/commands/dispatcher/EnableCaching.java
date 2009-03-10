package org.jmlspecs.jml4.esc.distribution.configuration.commands.dispatcher;

import org.jmlspecs.jml4.esc.distribution.configuration.FrontCommand;
import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.VcCache;

public class EnableCaching extends FrontCommand {

	@Override
	public void execute(CommandInput arg) throws FrontControllerException {
		VcCache.setEnabled(true);
	}

	
	
}
