package Dispatcher;

import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcDistributed;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.MalformedURLException;
import java.net.URLConnection;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

public class VCDispatcherThread extends Thread {
	
	private VCQueue queue;
	private int threadid;
	private static final String PROPERTIES_FILE = "dispatch";
	
	private static HashMap<VC, Result[]> results = new HashMap<VC, Result[]>();
	
	public VCDispatcherThread(int threadid, VCQueue v){
		this.threadid = threadid;
		queue = v;
	}

	public void run(){
		String key = null;
		
		key = "part." + threadid;
		String url = getUrlString(key);
		//write objects
		int times = 200000;
		int count = 0;
		while(times-->0){
			VC vc = queue.getNext();
			if(vc != null){
				new HTTPConnectionThread(vc, url).start();
				count++;
			}
			try {
				sleep(3);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		System.out.println(url + " " + count + " " + threadid + " " + key);
	}
	
	private static ResourceBundle bundle;
	protected synchronized static String getUrlString(String key) {
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
	
	public synchronized static void putResults(VC vc, Result[] rs){
		results.put(vc, rs);
	}
}
