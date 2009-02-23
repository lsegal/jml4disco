/*
 * ProveVcThread
 * 
 * Version 2.0 
 *
 * January 28th, 2009
 * 
 * Contributors:
 * R Le Guen, N Grigoropoulos, CJ Sheu
 */
package org.jmlspecs.jml4.esc.distribution.servers.vcprogram;

import java.util.Vector;

import org.jmlspecs.jml4.esc.Esc;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

/**
 * This thread is used to prove VC programs and accumulates the responses
 */
public class ProveVcThread implements Runnable {

	private VC vc;
	private VcProgram vcProg;
	private final int count;
	private Vector<Result> accumulator;
	private final int[] done;
	private AbstractRemoteServer server;

	public ProveVcThread(VC _vc, VcProgram _vcp, int _count,
			Vector<Result> acc, int[] _done, AbstractRemoteServer _server) {
		vcProg = _vcp;
		vc = _vc;
		count = _count;
		accumulator = acc;
		done = _done;
		server = _server;
	}

	public void run() {
		vc.setName(vcProg.methodIndicator + "_" + (count + 1)); //$NON-NLS-1$
		if (Esc.GEN_STATS)
			System.out
			.println("ESC4\tProveVcProgram\tpiece\tstart\t" + vc.getName() + "\t" + Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
		String[] prover = new String[1]; 
		Result[] results = VcCache.get(vc); 
		if(results == null){ 
			results = server.proveVc(count, vc, vcProg.incarnations, prover); 
			if (!Result.isValid(results)) { 
				for (int j = 0; j < results.length; j++) { 
					accumulator.add(results[j]); 
				} 
				//ADDED FOR CACHING 
				VcCache.add(vc, results, prover[0]); 
				//DONE WITH THE ADD 
			} 
			else{ 
				VcCache.add(vc, Result.VALID, prover[0]); 
			} 
		} 
		else{ 
			if (!Result.isValid(results)) { 
				for (int j = 0; j < results.length; j++) { 
					accumulator.add(results[j]); 
				} 
				synchronized (done) {
					done[0]++;
					done.notify();
				}
				if (Esc.GEN_STATS)
					System.out
					.println("ESC4\tProveVcProgram\tpiece\tend\t" + vc.getName() + "\t" + Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
			}
		}
	}
}
