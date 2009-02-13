package org.jmlspecs.jml4.esc.distribution.servers.vc;

import java.io.Serializable;

import org.jmlspecs.jml4.esc.distribution.IServerProfile;
import org.jmlspecs.jml4.esc.result.lang.Result;

public class ProveVcServerResult implements Serializable {

	private IServerProfile serverProfile;
	private Result[] result = Result.EMPTY;
	
	public ProveVcServerResult(IServerProfile serverProfile, Result[] result) {

		this.serverProfile = serverProfile;
		this.result = result;

	}

	public IServerProfile getServerProfile() {
		return serverProfile;
	}

	public Result[] getResult() {
		return result;
	}
	
}
