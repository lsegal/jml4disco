package org.jmlspecs.jml4.esc.distribution.http.config.servlets;

import java.util.Map;

import javax.servlet.http.HttpServletRequest;

import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;

public class HttpRequestCommandInput implements CommandInput {

	private HttpServletRequest request;
	private String commandName;
	
	public HttpRequestCommandInput(HttpServletRequest request, String commandName) {
		this.request = request;
		this.commandName = commandName;
	}
	
	@Override
	public Object getAttribute(String name) {
		return request.getAttribute(name);
	}

	@Override
	public String getCommandName() {
		return commandName;
	}

	@Override
	public String getParameter(String name) {
		return request.getParameter(name);
	}

	@Override
	public Map getParameterMap() {
		return request.getParameterMap();
	}

	@Override
	public void removeAttribute(String name) {
		request.removeAttribute(name);
	}

	@Override
	public void setAttribute(String name, Object o) {
		request.setAttribute(name, o);
	}

}