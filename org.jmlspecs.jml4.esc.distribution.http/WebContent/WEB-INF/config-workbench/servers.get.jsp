<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8" import="java.util.List,org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer" %>
<h2>Remote Servers:</h2>
<div>
These are the remote machines to which this Dispatcher dispatches.
</div>
<%
	Object obj = request.getAttribute("Servers");
	if(obj!=null && obj instanceof List) {
		List<AbstractRemoteServer> servers = (List<AbstractRemoteServer>)obj;
		out.println("<ul>");
		for(AbstractRemoteServer server:servers) {
			out.println("<li>"+server+"</li>");
		}
		out.println("</ul>");
	}
%>