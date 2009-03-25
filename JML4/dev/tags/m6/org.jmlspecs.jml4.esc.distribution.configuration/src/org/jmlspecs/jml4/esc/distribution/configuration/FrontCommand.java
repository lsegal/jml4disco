package org.jmlspecs.jml4.esc.distribution.configuration;

import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;

public abstract class FrontCommand {

	public abstract void execute(CommandInput arg) throws FrontControllerException;
	
}
