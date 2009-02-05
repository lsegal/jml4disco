package org.jmlspecs.jml4.esc.distribution.configuration;

public abstract class FrontCommand {

	public abstract void execute(CommandInput arg) throws FrontControllerException;
	
}
