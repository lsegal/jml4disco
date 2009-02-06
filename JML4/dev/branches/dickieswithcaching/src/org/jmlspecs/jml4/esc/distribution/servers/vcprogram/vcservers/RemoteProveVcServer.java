package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers;

import java.util.Map;

import org.jmlspecs.jml4.esc.distribution.IServerProfile;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public abstract class RemoteProveVcServer implements IServerProfile {
	
	public abstract Result[] proveVc(int i, VC vc, Map<String, Integer> map);
	
}
