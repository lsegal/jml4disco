package org.jmlspecs.jml4.esc.distribution.www.servlets;


import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import javax.servlet.ServletConfig;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.jmlspecs.jml4.esc.Esc;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.VcProgramDispatchingServer;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

/**
 * Servlet implementation class ProveVcProgram
 */
public class ProveVcProgram extends HttpServlet {
	private static final long serialVersionUID = 1L;
	public static final int NUMBER_OF_THREADS = 64;
       
	public void init(ServletConfig config) throws ServletException {
	    super.init(config);
	}   
	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		processRequest(request, response);
	}
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		processRequest(request, response);
	}
	
	private static int id = (int)(Math.random() * 10000);
   protected void processRequest (HttpServletRequest request, HttpServletResponse response)throws ServletException, IOException {
	   
	   System.out.println("DickieESC4Web processRequest");
	   
	   Esc.GEN_STATS = false;
		String contentType = "application/x-java-serialized-object";  
		response.setContentType(contentType);
		
		Result[] result = Result.EMPTY;
		ObjectInputStream in = null;
		VcProgram vcProg;
		try {
			if (request.getContentLength() != -1) {
				in = new ObjectInputStream(request.getInputStream());
				vcProg = (VcProgram) in.readObject();
				result = VcProgramDispatchingServer.proveVcProgram(vcProg);
			}			

		} catch (Exception e) {
			e.printStackTrace();
		}
		
		response.setContentType(contentType);
		ObjectOutputStream out = new ObjectOutputStream(response.getOutputStream());  	   
		out.writeObject(result);
		out.flush();
		out.close();
		
		System.out.println("DONE DickieESC4Web processRequest");

	}
}