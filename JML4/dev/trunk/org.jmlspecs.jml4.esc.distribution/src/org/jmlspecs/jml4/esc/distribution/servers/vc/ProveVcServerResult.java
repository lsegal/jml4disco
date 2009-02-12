package org.jmlspecs.jml4.esc.distribution.servers.vc;

import java.io.Serializable;

import org.jmlspecs.jml4.esc.distribution.IServerProfile;
import org.jmlspecs.jml4.esc.result.lang.Result;

public class ProveVcServerResult implements Serializable {

	private IServerProfile serverProfile;
	private Result[] result = Result.EMPTY;
	private String prover = "";
	
	public ProveVcServerResult(IServerProfile serverProfile, Result[] result, String prover) {

		this.serverProfile = serverProfile;
		this.result = result;
		this.prover = prover;

	}

	public IServerProfile getServerProfile() {
		return serverProfile;
	}

	public Result[] getResult() {
		return result;
	}
	
	public String getProver(){
		return prover;
	}
	
}
