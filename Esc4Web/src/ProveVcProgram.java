

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.MalformedURLException;
import java.net.URLConnection;
import java.util.Map;
import java.util.MissingResourceException;
import java.util.ResourceBundle;
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
	private static final String PROPERTIES_FILE = "dispatch";
    private final Executor executor = Executors.newFixedThreadPool(NUMBER_OF_THREADS);
       
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
				result = provePiecewise(vcProg);
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
 
   public Result[] provePiecewise(final VcProgram vcProg) {
	   final VC[] vcs = vcProg.getAsImplications();
	   final Vector<Result> accumulator = new Vector<Result>();
	   final int[] done = new int[1];
	   if (Esc.GEN_STATS)
			  System.out.println("ESC4\tProveVcProgram\tloop\tstart\t"+vcProg.methodIndicator+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
	   for (int i = 0; i < vcs.length; i++) {
		   final VC vc = vcs[i];
		   final int count = i;
		   Runnable work = new Runnable() {
			   public void run() {
				   vc.setName(vcProg.methodIndicator + "_" + (count + 1)); //$NON-NLS-1$
				   if (Esc.GEN_STATS)
						  System.out.println("ESC4\tProveVcProgram\tpiece\tstart\t"+vc.getName()+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
				   Result[] results = proveVc(count, vc, vcProg.incarnations);
				   if (! Result.isValid(results)) {
					   for (int j = 0; j < results.length; j++) {
						   accumulator.add(results[j]);
					   }
				   }
				   synchronized (done) {
					   done[0]++;
					   done.notify();
				   }
				   System.out.println("did work "+count);
				   if (Esc.GEN_STATS)
						  System.out.println("ESC4\tProveVcProgram\tpiece\tend\t"+vc.getName()+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
			   }
		   };
		   executor.execute(work);
	   }
	   if (Esc.GEN_STATS)
			  System.out.println("ESC4\tProveVcProgram\tloop\tend\t"+vcProg.methodIndicator+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
	   Esc.waitForItToFinish(done, vcs.length);
	   if (accumulator.size() == 0)
		   accumulator.add(Result.VALID[0]);
	   if (Esc.GEN_STATS)
			  System.out.println("ESC4\tProveVcProgram\twaited\tstart\t"+vcProg.methodIndicator+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
	   return (Result[])accumulator.toArray(Result.EMPTY);
   }
	public Result[] proveVc(int i, VC vc, Map<String, Integer> map) {
		String key = null;
		try {
			//URL CONNECTION SETUP
			//URL url = new URL("http://localhost:8080/EscWeb/EscWebServlet"); //$NON-NLS-1$
			//URL url = new URL("http://localhost:8080/ProverCoordinator/ProverCoordinator"); //$NON-NLS-1$

			int prover = (i % 10) + 1;
			key = "part." + prover;
			URLConnection conn = ProveVcDistributed.getUrlConnection(getUrlString(key));
			ObjectOutputStream out = new ObjectOutputStream(conn.getOutputStream());
			//write objects
			out.writeObject(vc);
			out.writeObject(map);
			out.flush();
			out.close();
			//read response
			ObjectInputStream in = null;
			in = new ObjectInputStream(conn.getInputStream());
			Result[] rs = Result.EMPTY;
			if (in != null) {
				rs = (Result[]) in.readObject();			
			}
			System.out.println("back_from_proveVc__");
			return rs;
			

		}
		catch ( MalformedURLException ex ) {
			// a real program would need to handle this exception
		}
		catch ( IOException ex ) {
			// a real program would need to handle this exception
			System.out.println("Key is: "+ key);
			//System.out.println("URL String is:" + ProveVcDistributed.getUrlString(key) );
			System.out.println(ex);
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}
	
	private static ResourceBundle bundle;
	private synchronized static String getUrlString(String key) {
	    try {
	    	if (bundle == null) {
	    		bundle = ResourceBundle.getBundle(PROPERTIES_FILE);
	    	}
	    	
	        return bundle.getString(key);
	    } catch (MissingResourceException e) {
	    	e.printStackTrace();
	    	return null;
	    }
	}
}