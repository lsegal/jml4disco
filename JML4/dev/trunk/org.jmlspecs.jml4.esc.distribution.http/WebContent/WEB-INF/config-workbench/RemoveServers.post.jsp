<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>

Response: 
<%= request.getAttribute("out") %>

<table>
<%
Object[] servers = (Object[])request.getAttribute("servers");
for(int i=0; i<servers.length; i++) {
	out.println("<tr>");
	out.println("<td>");
	out.println(servers[i].toString());
	out.println("</td>");
	out.println("<td>");
	out.println("<form action='RemoveServers' method='POST'><input type='hidden' name='server-name' balue='"+servers[i].toString()+"' /><input type='submit' value='delete' /></form>");
	out.println("</td>");
	out.println("</tr>");
}
%>
</table>
