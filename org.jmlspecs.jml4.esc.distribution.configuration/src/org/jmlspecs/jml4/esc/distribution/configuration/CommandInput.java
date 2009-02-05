package org.jmlspecs.jml4.esc.distribution.configuration;

import java.util.Map;

public interface CommandInput {
	
	public Object getAttribute(String name);
	public String getParameter(String name);
	public Map getParameterMap();
	public void removeAttribute(String name);
	public void setAttribute(String name, Object o);
	public String getCommandName();
	
}
