package org.jmlspecs.jml4.esc.distribution.http.servlets;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream; 
import java.util.Map;

import javax.servlet.ServletConfig;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.jmlspecs.jml4.esc.Esc;
//import org.jmlspecs.jml4.esc.distribution.ServerProfile;
import org.jmlspecs.jml4.esc.distribution.ServerProfile;
import org.jmlspecs.jml4.esc.distribution.servers.vc.ProveVcServer;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;

/**
 * Servlet implementation class ProveVc
 */
public class ProveVc extends HttpServlet {
	private static final long serialVersionUID = 1L;
	
	public synchronized void init(ServletConfig config) throws ServletException {
	    super.init(config);  
	}   
	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		processRequest(request, response);
	}
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		processRequest(request, response);
	}
	private static int id = (int)(Math.random() * 10000);
	
   @SuppressWarnings("unchecked")
    protected void processRequest (HttpServletRequest request, HttpServletResponse response)throws ServletException, IOException {
	   
	   Esc.GEN_STATS = false;
	   
		String contentType = "application/x-java-serialized-object";  

		Result[] result = Result.EMPTY;
		ObjectInputStream in = null;
		VC vc = null;
		Map<String, Integer> map;
		try {
			if (request.getContentLength() != -1) {
				in = new ObjectInputStream(request.getInputStream());
				vc = (VC) in.readObject();
				map = (Map<String, Integer>) in.readObject();
				result = ProveVcServer.prove(vc, map);
			} 

		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		}
		
		response.setContentType(contentType);
		ObjectOutputStream out = new ObjectOutputStream(response.getOutputStream());  	   
		out.writeObject(result);
		ServerProfile profile = new ServerProfile(); // added by Dickie on Fri Nov 28th 2:00pm-ish
		out.writeObject(profile);
		out.flush();
		out.close();
			   
//		   response.setContentType("text/html");
//		   PrintWriter out = response.getWriter();
//		   out.println("Hello web (from the servlet)! "+ value);
//		   out.close();	   
   		}
}