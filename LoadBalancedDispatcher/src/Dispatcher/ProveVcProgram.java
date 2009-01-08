package Dispatcher;



import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.MalformedURLException;
import java.net.URLConnection;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;
import java.util.concurrent.Executor;
import java.util.concurrent.Executors;

import javax.servlet.ServletConfig;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.jmlspecs.jml4.esc.Esc;
import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcDistributed;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;
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
	   int my_id;
	   synchronized(ProveVcProgram.class) {
		   my_id = id++;
	   }
	   if (Esc.GEN_STATS)
			  System.out.println("ESC4\tProveVcProgram\tstart\t"+my_id+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ 
		String contentType = "application/x-java-serialized-object";  
		response.setContentType(contentType);
		
		Result[] result = Result.EMPTY;
		ObjectInputStream in = null;
		VcProgram vcProg;
		try {
			if (request.getContentLength() != -1) {
				in = new ObjectInputStream(request.getInputStream());
					vcProg = (VcProgram) in.readObject();
				if (Esc.GEN_STATS)
				   System.out.println("ESC4\tProveVcProgram\tlink\t"+vcProg.methodIndicator+"\t"+my_id+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
				result = new DispatchVcProgram().dispatchVcProgram(vcProg);
			}			

		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		}
		
		response.setContentType(contentType);
		ObjectOutputStream out = new ObjectOutputStream(response.getOutputStream());  	   
		out.writeObject(result);
		out.flush();
		out.close();
	    if (Esc.GEN_STATS)
		   System.out.println("ESC4\tProveVcProgram\tend\t"+my_id+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ 
   }
}
