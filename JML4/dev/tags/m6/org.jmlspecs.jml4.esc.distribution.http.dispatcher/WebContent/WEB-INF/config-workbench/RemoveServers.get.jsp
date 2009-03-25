<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8"%>
<p>
These are the server URL's currently registered with the system.<br>
To remove one from getting distributed to, simply click the appropriate delete button.
</p>
<table>
<%
Object[] servers = (Object[])request.getAttribute("servers");
for(int i=0; i<servers.length; i++) {
	out.println("<tr>");
	out.println("<td>");
	out.println(servers[i].toString());
	out.println("</td>");
	out.println("<td>");
	out.println("<form action='RemoveServers' method='POST'><input type='hidden' name='server-name' value='"+servers[i].toString()+"' /><input type='submit' value='delete' /></form>");
	out.println("</td>");
	out.println("</tr>");
}
%>
</table>