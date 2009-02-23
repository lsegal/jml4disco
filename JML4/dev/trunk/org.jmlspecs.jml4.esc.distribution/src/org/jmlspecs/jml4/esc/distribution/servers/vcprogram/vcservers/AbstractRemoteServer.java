/*
 * AbstractRemoteServer
 * 
 * Version 2.0 
 *
 * January 28th, 2009
 * 
 * Contributors:
 * R Le Guen, N Grigoropoulos
 */
package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers;

import java.util.Map;

import org.jmlspecs.jml4.esc.distribution.IServerProfile;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;

/**
 * All RemoteServer implementations should inherit from here. To do so ensures
 * that they will all be forced to implement IServerProfile.
 */
public abstract class AbstractRemoteServer implements IServerProfile {

	public abstract Result[] proveVc(int i, VC vc, Map<String, Integer> map, String[] prover);
	public abstract long timeSinceLastProve();

}
