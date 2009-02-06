package org.jmlspecs.jml4.esc.distribution.servers.vcprogram;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.MissingResourceException;
import java.util.ResourceBundle;
import java.util.Vector;
import java.util.concurrent.Executor;
import java.util.concurrent.Executors;

import org.jmlspecs.jml4.esc.Esc;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.RemoteProveVcServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.implementations.RemoteProveVcTomCatServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.RemoteProveVcServerQueueFactory;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.implementations.RemoteProveVcServerQueue;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class ProveVcProgramServer {

	private static HashSet<RemoteProveVcServer> servers = initServersVar();
	private static final String PROPERTIES_FILE = "dispatch";
	
	private static int THREAD_POOL_SIZE = 75;
	private static Executor proveVcThreadPool = initProveVcThreadPool();

	public static Result[] proveVcProgram(final VcProgram vcProg) {
		RemoteProveVcServerQueue _servers = RemoteProveVcServerQueueFactory.newRemoteProveVcServerQueue(servers);
		final VC[] tvcs = vcProg.getAsImplications();
		final Vector<Result> accumulator = new Vector<Result>();
		//Added for caching
		ArrayList<VC> avcs = new ArrayList<VC>();
		for(VC v:tvcs){
			if(VcCache.getInstance().contains(v)){
				for(Result r:VcCache.getInstance().get(v))
					accumulator.add(r);
			}
			else
				avcs.add(v);
		}
		
		final VC[] vcs = new VC[avcs.size()];
		for(int i=0;i<vcs.length;i++)
			vcs[i] = avcs.get(i);
		 //DONE WITH THE ADD
		
		
		
		final int[] done = new int[1];
		for (int i = 0; i < vcs.length; i++) {
			final VC vc = vcs[i];

			RemoteProveVcServer server = null;
			//server = _servers.remove();
			server = _servers.peek();
			System.out.println("\tSending to server "+server.toString());
			Runnable work = new ProveVcThread(vc, vcProg, i, accumulator, done, server);
			proveVcThreadPool.execute(work);

			//_servers.add(server);
		}
		Esc.waitForItToFinish(done, vcs.length);
				
		if (accumulator.size() == 0)
			accumulator.add(Result.VALID[0]);
		
		return (Result[])accumulator.toArray(Result.EMPTY);
	}
	
	private static Executor initProveVcThreadPool() {
		return Executors.newFixedThreadPool(THREAD_POOL_SIZE);
	}
	
	private static HashSet<RemoteProveVcServer> initServersVar() {
		try {
			ResourceBundle bundle = ResourceBundle.getBundle(PROPERTIES_FILE);
	    	
			// TODO check that numberOfServers key exists
	    	int numberOfServers = Integer.parseInt(bundle.getString("numberOfServers"));
	    	HashSet<RemoteProveVcServer> _servers = new HashSet<RemoteProveVcServer>();
	    	for(int i=1; i<=numberOfServers; i++) {
	    		_servers.add(new RemoteProveVcTomCatServer(bundle.getString("vcServer."+i)));
	    	}
	    	return _servers;
	    	
	    } catch (MissingResourceException e) {
	    	e.printStackTrace();
	    }
	    return null;
	}

}
