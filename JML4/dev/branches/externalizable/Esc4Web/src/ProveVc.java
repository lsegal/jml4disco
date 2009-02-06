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
import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcPiecewise;
import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcPiecewise_timings;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;

/**
 * Servlet implementation class ProveVc
 */
public class ProveVc extends HttpServlet {
	private static final long serialVersionUID = 1L;
       
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
   @SuppressWarnings("unchecked")
    protected void processRequest (HttpServletRequest request, HttpServletResponse response)throws ServletException, IOException {
	   int my_id;
	   synchronized(ProveVcProgram.class) {
		   my_id = id++;
	   }
	   if (Esc.GEN_STATS)
			  System.out.println("ESC4\tProveVc\tstart\t"+my_id+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ 
		String contentType = "application/x-java-serialized-object";  
		response.setContentType(contentType);
		
		Result[] result = Result.EMPTY;
		ObjectInputStream in = null;
		VC vc = null;
		Map<String, Integer> map;
		try {
			if (request.getContentLength() != -1) {
				in = new ObjectInputStream(request.getInputStream());
				String vcClassName = in.readUTF();
				Class c = Class.forName(vcClassName);
				Object o = c.newInstance();
				vc = (VC) o;
				vc.readExternal(in);
				map = (Map<String, Integer>) in.readObject();
				if (Esc.GEN_STATS)
					   System.out.println("ESC4\tProveVc\tlink\t"+vc.getName()+"\t"+my_id+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
				ProveVcPiecewise proveVcPiece= new ProveVcPiecewise(null, null, null);
				result = proveVcPiece.proveVc(vc, map);
			}			

		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		} catch (InstantiationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		response.setContentType(contentType);
		ObjectOutputStream out = new ObjectOutputStream(response.getOutputStream());  	   
		out.writeObject(result);
		out.flush();
		out.close();
			   
//		   response.setContentType("text/html");
//		   PrintWriter out = response.getWriter();
//		   out.println("Hello web (from the servlet)! "+ value);
//		   out.close();	   
		System.out.println("handling part with hashcode '"+(vc==null?vc:vc.hashCode())+"'");
		   if (Esc.GEN_STATS)
		      System.out.println("ESC4\tProveVc\tend\t"+my_id+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ 
   		}
}