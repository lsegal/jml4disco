/*
 * RemoteTomCatServer
 * 
 * Version 2.0 
 *
 * January 28th, 2009
 * 
 * Contributors:
 * R Le Guen
 */
package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.implementations;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.HttpURLConnection;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.Map;

import org.jmlspecs.jml4.esc.distribution.IServerProfile;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class RemoteTomCatServer extends AbstractRemoteServer{

	private IServerProfile profileInfo;
	private URL url;
	
	private int pendingRequests;
	
	public RemoteTomCatServer(String _url) {
		try {
			url = new URL (_url);
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		profileInfo = new IServerProfile() {

			@Override
			public int getAvailableProcessors() {
				// TODO Auto-generated method stub
				return 0;
			}

			@Override
			public long getCommittedVirtualMemorySize() {
				// TODO Auto-generated method stub
				return 0;
			}

			@Override
			public long getFreePhysicalMemorySize() {
				// TODO Auto-generated method stub
				return 0;
			}

			@Override
			public long getFreeSwapSpaceSize() {
				// TODO Auto-generated method stub
				return 0;
			}

			@Override
			public int getPendingVcs() {
				// TODO Auto-generated method stub
				return 0;
			}

			@Override
			public long getProcessCpuTime() {
				// TODO Auto-generated method stub
				return 0;
			}

			@Override
			public double getSystemLoadAverage() {
				// TODO Auto-generated method stub
				return 0.0001;
			}

			@Override
			public long getTotalPhysicalMemorySize() {
				// TODO Auto-generated method stub
				return 0;
			}
			
		};
	}
	
	@Override
	public Result[] proveVc(int i, VC vc, Map<String, Integer> map) {
		pendingRequests++;
		try {
			HttpURLConnection conn = (HttpURLConnection) url.openConnection();
			conn.setDoInput(true); 
			conn.setDoOutput(true);
			conn.setUseCaches(false);  
			conn.setDefaultUseCaches(false);
			conn.setRequestProperty("Content-Type", "application/x-java-serialized-object");  //$NON-NLS-1$
			ObjectOutputStream out = new ObjectOutputStream(conn.getOutputStream());
			//write objects
			out.writeObject(vc);
			out.writeObject(map);
			out.flush();
			out.close();
			//read response
			ObjectInputStream in = null;
			in = new ObjectInputStream(conn.getInputStream());
			Result[] rs = Result.EMPTY;
			if (in != null) {
				rs = (Result[]) in.readObject();
				setProfileInfo((IServerProfile) in.readObject());
			}
			in.close();
			conn.disconnect();
			System.out.println("back_from_proveVc__");
			pendingRequests--;
			
			return rs;
		}
		catch ( MalformedURLException ex ) {
			// a real program would need to handle this exception
			System.out.println("Exception in "+this);
			ex.printStackTrace();
		}
		catch ( IOException ex ) {
			// a real program would need to handle this exception
			System.out.println("Exception in "+this);
			ex.printStackTrace();
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		pendingRequests--;
		return null;
	}
	
	private void setProfileInfo(IServerProfile profile) {
		this.profileInfo = profile;
	}

	@Override
	public int getAvailableProcessors() {
		return profileInfo.getAvailableProcessors();
	}

	@Override
	public long getCommittedVirtualMemorySize() {
		return profileInfo.getCommittedVirtualMemorySize();
	}

	@Override
	public long getFreePhysicalMemorySize() {
		return profileInfo.getFreePhysicalMemorySize();
	}

	@Override
	public long getFreeSwapSpaceSize() {
		return profileInfo.getFreeSwapSpaceSize();
	}

	@Override
	public int getPendingVcs() {
		int pendingVcs = profileInfo.getPendingVcs();
		if(pendingVcs==0) {
			return pendingRequests;
		}
		else {
			return pendingVcs;
		}
	}

	@Override
	public long getProcessCpuTime() {
		return profileInfo.getProcessCpuTime();
	}

	@Override
	public double getSystemLoadAverage() {
		return profileInfo.getSystemLoadAverage();
	}

	@Override
	public long getTotalPhysicalMemorySize() {
		return profileInfo.getTotalPhysicalMemorySize();
	}

	public String toString() {
		return "Remote ProveVC Tomcat Server: "+url;
	}
}
