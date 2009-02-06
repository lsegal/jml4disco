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
		// TODO Auto-generated method stub
		String webroot = request.getContextPath()+request.getServletPath();
		try {
			
			if(request.getRequestURI().substring(0, webroot.length()).equals(webroot)) {
				String in = request.getRequestURI().substring(webroot.length());
				if(in.length()>0 && in.charAt(0)=='/') {
					in = in.substring(1);
				}

				String path = "/WEB-INF/config-workbench/"+in+".get.jsp";
				String filename = getServletConfig().getServletContext().getRealPath(path);
				File f = new File(filename); 
				if(f.exists()) {
					PrintWriter response_out = response.getWriter();
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
					response.getWriter().println("<!--added from the servlet-->");
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
			}
			else {
				throw new ServletException("Unable to determine requested resource.");
			}
		} catch (IOException e) {
			throw new ServletException(e);
		}
	}

	/**
	 * @see HttpServlet#doPost(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		String webroot = request.getContextPath()+request.getServletPath();
		String out = "";
		String command = "";
		try {
			if(request.getRequestURI().substring(0, webroot.length()).equals(webroot)) {
				String in = request.getRequestURI().substring(webroot.length());
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
			}
			else {
				throw new ServletException("Unable to determine command name.");
			}
		} catch(CommandNotFoundException e) {
			response.setStatus(404);
			return;
		} catch (FrontControllerException e) {
			out = "Unable to fullfill the request: "+e.getMessage();
		}
		
		request.setAttribute("out", out);
		
		try {
			PrintWriter response_out = response.getWriter();
			response_out.println("<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\" \"http://www.w3.org/TR/html4/loose.dtd\">");
			response_out.println("<html>");
			response_out.println("<head>");
			response_out.println("<meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\">");
			response_out.println("<title>JML4 Disco Configuration Interface | "+command+"</title>");
			response_out.println("<title>JML4 Disco Configuration Interface | "+command+"</title>");
			response_out.println("</head>");
			response_out.println("<body>");
			getServletConfig().getServletContext().getRequestDispatcher("/WEB-INF/config-workbench/"+command+".post.jsp").include(request,response);
			response.getWriter().println("<!--added from the servlet-->");
			response_out.println("</body>");
			response_out.println("</html>");
		} catch (IOException e) {
			throw new ServletException(e);
		}
		
	}

}
