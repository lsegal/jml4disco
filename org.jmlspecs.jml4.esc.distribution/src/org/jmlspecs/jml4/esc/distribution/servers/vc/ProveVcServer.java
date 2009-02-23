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
	
	public static ProveVcServerResult prove(VC vc, Map<?,?> map) {
		ServerProfile.incrementPending();
		ProveVcPiecewise proveVcPiece= new ProveVcPiecewise(null, null, null);
		String[] prover = new String[1]; 
	 	Result[] result = proveVcPiece.proveVc(vc, map, prover);
		System.out.println("\n\tVcServer done...");
		ServerProfile.decrementPending();
		ServerProfile profile = new ServerProfile(); // added by Dickie on Fri Nov 28th 2:00pm-ish
		ProveVcServerResult toReturn = new ProveVcServerResult(profile, result, prover[0]);
		return toReturn;
	}

}
