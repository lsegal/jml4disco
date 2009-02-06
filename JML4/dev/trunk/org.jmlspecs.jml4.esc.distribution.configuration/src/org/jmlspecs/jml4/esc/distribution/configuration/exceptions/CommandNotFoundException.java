package org.jmlspecs.jml4.esc.distribution.configuration.exceptions;


public class CommandNotFoundException extends FrontControllerException {

	public CommandNotFoundException() {
		super();
	}
	
	public CommandNotFoundException(String s) {
		super(s);
	}
	
	public CommandNotFoundException(Exception e) {
		super(e);
	}
	
	public CommandNotFoundException(String s, Exception e) {
		super(s, e);
	}
	
}
