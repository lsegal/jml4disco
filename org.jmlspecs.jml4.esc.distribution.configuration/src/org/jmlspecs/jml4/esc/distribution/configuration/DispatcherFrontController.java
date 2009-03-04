package org.jmlspecs.jml4.esc.distribution.configuration;

import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.CommandNotFoundException;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;

public class DispatcherFrontController {
	
	public static void main(CommandInput commandInput) throws FrontControllerException, CommandNotFoundException {
		
		String command = commandInput.getCommandName();
		
		try {
			String commandpath = "org.jmlspecs.jml4.esc.distribution.configuration.commands.dispatcher"; 
			Class commandClass = Class.forName(commandpath+"."+command);
			
			if(FrontCommand.class.isAssignableFrom(commandClass)) {
				FrontCommand frontCommand = (FrontCommand) commandClass.newInstance();
				frontCommand.execute(commandInput);
			}
			else {
				throw new FrontControllerException("Unable to execute command '"+command+"'.");
			}
			
			
		} catch (ClassNotFoundException e) {
			throw new CommandNotFoundException("No such command '"+command+"'.", e);
		} catch (InstantiationException e) {
			throw new RuntimeException("Failed to execute command '"+command+"'.", e);
		} catch (IllegalAccessException e) {
			throw new RuntimeException("Failed to execute command "+command+".", e);
		}
		
	}
	
}
