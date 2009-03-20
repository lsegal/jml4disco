/*
 * VcProgramDispatchingServer
 * 
 * Version 2.0 
 *
 * January 28th, 2009
 * 
 * Contributors:
 * R Le Guen, N Grigoropoulos
 */
package org.jmlspecs.jml4.esc.distribution.servers.vcprogram;

import java.util.Vector;
import java.util.concurrent.Executor;
import java.util.concurrent.Executors;

import org.jmlspecs.jml4.esc.Esc;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerQueue;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerQueueRegistry;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

/**
 * This class proves VCprograms by breaking it into VC's and distributing the
 * workload amongst servers.
 */
public class VcProgramDispatchingServer {

	private static int THREAD_POOL_SIZE = initThreadPoolSize(); 	// The max number of threads in
												// the pool
	private static int THROTTLE_VALUE = initThrottleValue();		//The number of pending VC's before throttling
	private static int THROTTLE_TIME = initThrottleTime(); 	//In milliseconds
	
	private static Executor proveVcThreadPool = initProveVcThreadPool();

	/**
	 * This method is responsible for "breaking up" the VC program and sending
	 * the various pieces to the servers.
	 * 
	 * @param vcProg
	 *            The VCprogram to be proved.
	 * @return Will return a Result array.
	 */
	public static Result[] proveVcProgram(final VcProgram vcProg) {

		// Get the server queue
		ServerQueue _servers = ServerQueueRegistry
				.getRemoteProveVcServerQueueInstance();

		// Break up the VCProgram
		final VC[] vcs = vcProg.getAsImplications();
		final Vector<Result> accumulator = new Vector<Result>();
		final int[] done = new int[1];
		AbstractRemoteServer server = null;
		boolean retry = false;
		// Start Dispatching
		for (int i = 0; i < vcs.length; i++) {
			final VC vc = vcs[i];
			
			do{
				server = _servers.peek();
				if(server.getPendingVcs() > THROTTLE_VALUE )  
				{ 	//This allows for delaying dispatching if the best server available is too
					// burdened with too many pending VCs
					retry = true;
					try {
						Thread.currentThread().sleep(THROTTLE_TIME);
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
				}
				else
					retry = false;
			} while(retry);
			
			System.out.println("\tSending to server " + server.toString());
			Runnable work = new ProveVcThread(vc, vcProg, i, accumulator, done,	server);
			proveVcThreadPool.execute(work);
		}
		Esc.waitForItToFinish(done, vcs.length);
		if (accumulator.size() == 0)
			accumulator.add(Result.VALID[0]);

		return (Result[]) accumulator.toArray(Result.EMPTY);
	}

	private static int initThrottleTime() {
		try {
			int i = Integer.parseInt(VcProgramDispatchingServerResources.getProperty("dispatchingThrottleWaitTime")); 
			return i;
		}
		catch(Exception e) {
			e.printStackTrace();
			return 1000;
		}
	}

	private static int initThrottleValue() {
		try {
			int i = Integer.parseInt(VcProgramDispatchingServerResources.getProperty("dispatchingThrottleLimit")); 
			return i;
		}
		catch(Exception e) {
			e.printStackTrace();
			return 25;
		}
	}

	private static int initThreadPoolSize() {
		try {
			int i = Integer.parseInt(VcProgramDispatchingServerResources.getProperty("dispatchingParallelRequestsLimit")); 
			return i;
		}
		catch(Exception e) {
			e.printStackTrace();
			return 75;
		}
	}

	private static Executor initProveVcThreadPool() {
		return Executors.newFixedThreadPool(THREAD_POOL_SIZE);
	}

}
