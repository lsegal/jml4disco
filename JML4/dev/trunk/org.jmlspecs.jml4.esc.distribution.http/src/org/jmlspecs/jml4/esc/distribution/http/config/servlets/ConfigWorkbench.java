package org.jmlspecs.jml4.esc.distribution.http.config.servlets;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.jmlspecs.jml4.esc.distribution.configuration.FrontController;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.CommandNotFoundException;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;

/**
 * Servlet implementation class Workbench
 */
public class ConfigWorkbench extends HttpServlet {
	private static final long serialVersionUID = 1L;

	/**
	 * @see HttpServlet#HttpServlet()
	 */
	public ConfigWorkbench() {
		super();
		// TODO Auto-generated constructor stub
	}

	/**
	 * @see HttpServlet#doGet(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		processRequest(request, response);
	}

	/**
	 * @see HttpServlet#doPost(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		processRequest(request, response);
	}
	
	protected void processRequest(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		String webroot = request.getContextPath()+request.getServletPath();
		String out = ""; // out will be a temporary variable being used to cheaply produce output... should be removed after a while.
		String command = "";
		String in = "";
		if(request.getRequestURI().substring(0, webroot.length()).equals(webroot)) {	// This servlet assumes that the Request URI starts with the context path followed by the Servlet Path.
																						// If that assumption does not hold, this servlet will not work.
			in = request.getRequestURI().substring(webroot.length());
		}
		else {
			throw new ServletException("Unable to determine command name.");
		}
		
		try {
			/*
			 * Here we are processing the requested URI...
			 */
				if(in.length()>0 && in.charAt(0)=='/') {
					in = in.substring(1);
				}

				String[] split = in.split("\\/");
				if(split.length==1) {
					command  = split[0];
					
					HttpRequestCommandInput commandInput = new HttpRequestCommandInput(request, command);
					FrontController.main(commandInput);
					out = "Executed command successfully";
					 
				}
				else {
					response.setStatus(404);
					return;
				}

		} catch(CommandNotFoundException e) {
			response.setStatus(404);
			return;
		} catch (FrontControllerException e) {
			out = "Unable to fullfill the request: "+e.getMessage();
		}
		
		request.setAttribute("out", out);
		
		try {
			String path = "/WEB-INF/config-workbench/"+in+"."+request.getMethod().toLowerCase()+".jsp";
			String filename = getServletConfig().getServletContext().getRealPath(path);
			File f = new File(filename); 
			if(f.exists()) {
				PrintWriter response_out = response.getWriter();
				/*
				 * This method currently contains some basic layout code... this will eventually be moved out of this class into another.
				 */
				response_out.println("<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\" \"http://www.w3.org/TR/html4/loose.dtd\">");
				response_out.println("<html>");
				response_out.println("<head>");
				response_out.println("<meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\">");
				response_out.println("<title>JML4 Disco Configuration Interface | "+in+"</title>");
				response_out.println("<meta name='keywords' content='' />");
				response_out.println("<meta name='description' content='' />");
				response_out.println("<link href='default.css' rel='stylesheet' type='text/css' />");
				response_out.println("</head>");
				response_out.println("<body>");
				response_out.println("<div id='header'>");
				response_out.println("<div id='menu'>");
				response_out.println("	<ul>");
				response_out.println("		<li><a href='index' title=''>JML4 Disco - Server Config</a></li>");
				response_out.println("		<li><a href='AddServers' title=''>Add Servers</a></li>");
				response_out.println("	</ul>");
				response_out.println("</div>");
				response_out.println("</div>");
				response_out.println("<div>");
				getServletConfig().getServletContext().getRequestDispatcher("/WEB-INF/config-workbench/"+in+".get.jsp").include(request,response);
				response_out.println("</div>");
				response_out.println("</body>");
				response_out.println("</html>");
			}
			else {
				path = "/WEB-INF/config-workbench/"+in;
				filename = getServletConfig().getServletContext().getRealPath(path);
				f = new File(filename); 
				if(f.exists()) {
					getServletConfig().getServletContext().getRequestDispatcher(path).include(request,response);
				}
				else {
					response.setStatus(404);
				}
			}
		} catch (IOException e) {
			throw new ServletException(e);
		}
	}

}
