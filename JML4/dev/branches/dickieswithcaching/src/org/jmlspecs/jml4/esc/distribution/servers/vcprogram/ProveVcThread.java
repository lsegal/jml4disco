package org.jmlspecs.jml4.esc.distribution.servers.vcprogram;

import java.util.Vector;

import org.jmlspecs.jml4.esc.Esc;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.RemoteProveVcServer;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class ProveVcThread implements Runnable {
	
	private VC vc;
	private VcProgram vcProg;
	private final int count;
	private Vector<Result> accumulator;
	private final int[] done;
	private RemoteProveVcServer server;
	
	public ProveVcThread(VC _vc, VcProgram _vcp, int _count, Vector<Result>  acc, int[] _done, RemoteProveVcServer _server) {
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
			System.out.println("ESC4\tProveVcProgram\tpiece\tstart\t"+vc.getName()+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
		Result[] results = server.proveVc(count, vc, vcProg.incarnations);		
		
		if (! Result.isValid(results)) {
			for (int j = 0; j < results.length; j++) {
				accumulator.add(results[j]);
			}
			//ADDED FOR CACHING
			VcCache.getInstance().put(vc, results);
			//DONE WITH THE ADD
		}
		else{
			VcCache.getInstance().put(vc, Result.VALID);
		}
		
		synchronized (done) {
			done[0]++;
			done.notify();
		}
		//System.out.println("did work "+count);
		if (Esc.GEN_STATS)
			System.out.println("ESC4\tProveVcProgram\tpiece\tend\t"+vc.getName()+"\t"+Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
	}
}
