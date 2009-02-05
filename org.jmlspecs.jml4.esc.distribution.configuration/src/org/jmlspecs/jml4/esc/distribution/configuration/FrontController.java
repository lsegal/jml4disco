package org.jmlspecs.jml4.esc.distribution.configuration;

import java.util.ResourceBundle;

public class FrontController {

	private static final String PROPERTIES_FILE = "jml4-disco-config";
	private static ResourceBundle bundle = initResourceBundle();
	
	public static void main(CommandInput commandInput) throws FrontControllerException {
		
		String command = commandInput.getCommandName();
		
		try {
			String commandpath = bundle.getString("command-path"); 
			Class commandClass = Class.forName(commandpath+"."+command);
			
			if(FrontCommand.class.isAssignableFrom(commandClass)) {
				FrontCommand frontCommand = (FrontCommand) commandClass.newInstance();
				frontCommand.execute(commandInput);
			}
			else {
				throw new FrontControllerException("Unable to execute command '"+command+"'.");
			}
			
			
		} catch (ClassNotFoundException e) {
			throw new FrontControllerException("No such command '"+command+"'.", e);
		} catch (InstantiationException e) {
			throw new RuntimeException("Failed to execute command '"+command+"'.", e);
		} catch (IllegalAccessException e) {
			throw new RuntimeException("Failed to execute command "+command+".", e);
		}
		
	}
	
	private static ResourceBundle initResourceBundle() {
		ResourceBundle props = ResourceBundle.getBundle(PROPERTIES_FILE);
		return props;
	}
	
}
