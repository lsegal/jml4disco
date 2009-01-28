/*
 * ProveVcServer
 * 
 * Version 2.0 
 *
 * January 28th, 2009
 * 
 * Contributors:
 * R Le Guen, N Grigoropoulos
 */
package org.jmlspecs.jml4.esc.distribution.servers.vc;

import java.util.Map;

import org.jmlspecs.jml4.esc.distribution.ServerProfile;
import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcPiecewise;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class ProveVcServer {
		
	private ProveVcServer() {
		
	}
	
	public static Result[] prove(VC vc, Map<?,?> map) {
		ServerProfile.incrementPending();
		ProveVcPiecewise proveVcPiece= new ProveVcPiecewise(null, null, null);
		Result[] result = proveVcPiece.proveVc(vc, map);
		System.out.println("\n\tVcServer done...");
		ServerProfile.decrementPending();
		return result;
	}

}
