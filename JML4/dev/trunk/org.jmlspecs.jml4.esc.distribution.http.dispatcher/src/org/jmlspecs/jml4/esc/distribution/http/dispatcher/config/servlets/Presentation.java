package org.jmlspecs.jml4.esc.distribution.http.dispatcher.config.servlets;

import java.io.IOException;

import javax.servlet.Servlet;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

public class Presentation {
	
	private static ThreadLocal<String> viewPath = new ThreadLocal<String>();
	private static String layoutJSP = "/WEB-INF/config-workbench/Layout.jsp";

	public static void render(Servlet servlet, HttpServletRequest request, HttpServletResponse response, String path) throws ServletException, IOException {
		viewPath.set(path);
		servlet.getServletConfig().getServletContext().getRequestDispatcher(layoutJSP).include(request,response);
		viewPath.remove();
	}
	
	public static String getViewPath() {
		return viewPath.get().toString();
	}
	
}
