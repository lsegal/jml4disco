package org.jmlspecs.jml4.esc.distribution.http.config.servlets;

import java.io.IOException;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.jmlspecs.jml4.esc.distribution.configuration.FrontController;
import org.jmlspecs.jml4.esc.distribution.configuration.FrontControllerException;

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
		processRequest(request, response);
	}

	/**
	 * @see HttpServlet#doPost(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		// TODO Auto-generated method stub
		processRequest(request, response);
	}

	protected void processRequest(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

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

					System.out.println("Command is "+command);
					
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
		} catch (FrontControllerException e) {
			out = "Unable to fullfill the request: "+e.getMessage();
		}
		
		request.setAttribute("out", out);
		
		try {
			getServletConfig().getServletContext().getRequestDispatcher("/WEB-INF/ConfigWorkbench/"+command+".jsp").include(request,response);
		} catch (IOException e) {
			throw new ServletException(e);
		}
		
	}

}
