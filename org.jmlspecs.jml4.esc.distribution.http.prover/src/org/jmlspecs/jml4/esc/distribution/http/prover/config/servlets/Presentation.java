package org.jmlspecs.jml4.esc.distribution.http.prover.config.servlets;

import java.io.IOException;
import java.io.PrintWriter;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.VcCache;

public class Presentation {

	public static void render(HttpServletRequest request, HttpServletResponse response, RequestDispatcher dispatcher) throws ServletException, IOException {
		PrintWriter response_out = response.getWriter();
		response_out.println("<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\" \"http://www.w3.org/TR/html4/loose.dtd\">");
		response_out.println("<html>");
		response_out.println("<head>");
		response_out.println("<meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\">");
		response_out.println("<title>JML4 Disco Configuration Interface | </title>");
		response_out.println("<meta name='keywords' content='' />");
		response_out.println("<meta name='description' content='' />");
		response_out.println("<style>");
		response_out.println("body { border: 0; background: #eee; }");
		response_out.println("#header { width: 100%; overflow-y: hidden; padding: 0px;height: 40px; }");
		response_out.println("#menu { width: 800px; float: left; font-family: sans-serif; }");
		response_out.println("#menu ul { list-style: none; padding: 0; margin: 0; float: left; }");
		response_out.println("#menu li { float: left; display: block; } ");
		response_out.println("#menu a { display: block; padding: 20px; float: left; }");
		response_out.println("#menu a:link, #menu a:visited { color: #555; text-decoration: none; }");
		response_out.println("#menu a:hover { color: #fff; background-color: #af0a0a; padding: 20px; text-decoration: none; }");
		response_out.println("</style>");
		response_out.println("</head>");
		response_out.println("<body>");
		response_out.println("<div id='header'>");
		response_out.println("<div id='menu'>");
		response_out.println("	<ul>");
		response_out.println("		<li><a href='index.jsp' title=''>JML4 Disco - Server Config</a></li>");
		response_out.println("		<li><a href='AddServers' title=''>Add Servers</a></li>");
		response_out.println("		<li><a href='RemoveServers' title=''>Remove Servers</a></li>");
		response_out.println("	</ul>");
		response_out.println("</div>");
		response_out.println("</div>");
		response_out.println("<div>");
		dispatcher.include(request,response);
		response_out.println("</div>");
		response_out.println("</body>");
		response_out.println("</html>");
	}
	
}
