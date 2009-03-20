package org.jmlspecs.jml4.esc.distribution.http.prover.config.servlets;

import java.io.File;
import java.io.IOException;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.jmlspecs.jml4.esc.distribution.configuration.ProverFrontController;
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
				ProverFrontController.main(commandInput);

				String path = "/WEB-INF/config-workbench/"+in+"."+request.getMethod().toLowerCase()+".jsp";
				String filename = getServletConfig().getServletContext().getRealPath(path);
				File f = new File(filename); 
				if(f.exists()) {
					Presentation.render(this, request, response, path);
				}
				else {
					throw new ServletException("No view for command "+command+".");
				}
			}

		} catch(CommandNotFoundException e) {
			
			try {

				String path = "/WEB-INF/config-workbench/public/"+in;
				String filename = getServletConfig().getServletContext().getRealPath(path);
				File f = new File(filename); 
				if(f.exists()) {
					if(filename.endsWith(".jsp")) {
						Presentation.render(this, request, response, path);
					}
					else {
						getServletConfig().getServletContext().getRequestDispatcher(path).include(request,response);
					}
				}
				else {
					response.setStatus(404);
				}
			} catch (IOException ioe) {
				throw new ServletException(ioe);
			}
			
			return;
		} catch (FrontControllerException e) {
			throw new ServletException(e);
		}
	}

}
