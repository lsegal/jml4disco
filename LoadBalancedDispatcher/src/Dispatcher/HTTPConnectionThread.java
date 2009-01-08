package Dispatcher;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.MalformedURLException;
import java.net.URLConnection;
import java.util.ArrayList;

import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcDistributed;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class HTTPConnectionThread extends Thread{
	
	private VC vc;
	private String url;
	
	public HTTPConnectionThread(VC vc, String url){
		this.vc = vc;
		this.url = url;
	}
	
	public void run(){
		try {
		URLConnection conn = ProveVcDistributed.getUrlConnection(url);
		
		ObjectOutputStream out = new ObjectOutputStream(conn.getOutputStream());
		
		out.writeObject(vc);
		out.writeObject(VCQueue.getVcProgram(vc).incarnations);
		out.flush();
		out.close();

		ObjectInputStream in = null;
		in = new ObjectInputStream(conn.getInputStream());
		Result[] rs = Result.EMPTY;
		if (in != null) {
			rs = (Result[]) in.readObject();			
		}
		in.close();
		conn.setConnectTimeout(0);
		//System.out.println("back_from_proveVc__");
		VCDispatcherThread.putResults(vc, rs);
		if (! Result.isValid(rs)) {
			ArrayList<Result> accumulator = DispatchVcProgram.getAccumulator(VCQueue.getVcProgram(vc));
			   for (int j = 0; j < rs.length; j++) {
				   accumulator.add(rs[j]);
			   }
		   }		
		DispatchVcProgram.incrementDone(VCQueue.getVcProgram(vc));
	}
	catch ( MalformedURLException ex ) {
		// a real program would need to handle this exception
	}
	catch ( IOException ex ) {
		// a real program would need to handle this exception
		System.out.println(ex);
		ex.printStackTrace();
	} catch (ClassNotFoundException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	} catch (Exception e) {
		e.printStackTrace();
	}
	}

}
