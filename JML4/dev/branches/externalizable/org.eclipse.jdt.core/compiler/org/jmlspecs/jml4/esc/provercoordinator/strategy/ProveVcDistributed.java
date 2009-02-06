// DISCO _New distributed strategy VCs sent out to servlet here
package org.jmlspecs.jml4.esc.provercoordinator.strategy;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLConnection;
import java.util.Properties;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class ProveVcDistributed implements IProverStrategy {
	private CompilerOptions options;
	private ProblemReporter problemReporter;
	
	public ProveVcDistributed(CompilerOptions options, ProblemReporter problemReporter) {
		super();
		this.options = options;
		this.problemReporter = problemReporter;
	}

	public static String getName() {
		return "ProveVcDistributed"; //$NON-NLS-1$
	}

	public Result[] prove(VcProgram vcProg) {
		Result[] rs = proveRemotely(vcProg);
		if (rs == null || rs.length == 0)
			return Result.VALID;
		return rs;
	}

	public String toString() {
		return "[ProveVcDistributed: (Simplify, CVC3, Isabelle)]"; //$NON-NLS-1$
	}

	private Result[] proveRemotely (VcProgram vcProg) {
		try {
			//URL CONNECTION SETUP
			//URL url = new URL("http://localhost:8080/EscWeb/EscWebServlet"); //$NON-NLS-1$
			//URL url = new URL("http://localhost:8080/ProverCoordinator/ProverCoordinator"); //$NON-NLS-1$

			URLConnection conn = getUrlConnection(getUrlString("whole"));
			ObjectOutputStream out = new ObjectOutputStream(conn.getOutputStream());
			//write objects
			vcProg.writeExternal(out);
			out.flush();
			out.close();
			//read response
			ObjectInputStream in = null;
			in = new ObjectInputStream(conn.getInputStream());
			Result[] rs = null;
			if (in != null) {
				rs = (Result[]) in.readObject();
			}
			return rs;
			

		}
		catch ( MalformedURLException ex ) {
			// a real program would need to handle this exception
		}
		catch ( IOException ex ) {
			// a real program would need to handle this exception
			System.out.println(ex);
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}
	
	private String getUrlString(String key) {
	    // Read properties file.
	    Properties properties = new Properties();
	    try {
	    	File file = new File(options.jmlEscDistributedPropertiesFile);
	    	System.out.println(file.getAbsolutePath());
	        properties.load(new FileInputStream(file));
	        return (String) properties.get(key);
	        
	    } catch (IOException e) {
	    	e.printStackTrace();
	    	return null;
	    }
	    
	}
	
	public static URLConnection getUrlConnection (String strUrl) {
		URL url = null;
		try {
			url = new URL (strUrl);
			String contentType = "application/x-java-serialized-object";   //$NON-NLS-1$
	        URLConnection conn;
	        conn = url.openConnection();
			conn.setDoInput(true); 
			conn.setDoOutput(true);
			conn.setUseCaches(false);  
			conn.setDefaultUseCaches(false);
			conn.setRequestProperty("Content-Type", contentType);  //$NON-NLS-1$
			return conn;
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}
		catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}		
		
		
	}
	
}
