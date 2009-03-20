package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.technicalservices;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.VcProgramDispatchingServerResources;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerQueueRegistry;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.ServerQueueRegistryException;

public class RemoteServersMapper {

	public static AbstractRemoteServer[] findAll() throws IOException {
		File dir = new File(VcProgramDispatchingServerResources.getProperty("remoteProversDirectory"));
		if(!dir.isDirectory() || !dir.canRead()) {
			throw new IOException("Invalid configuration for 'remoteProversDirectory'.");
		}
		File[] files = dir.listFiles();
		
		AbstractRemoteServer[] toreturn = new AbstractRemoteServer[files.length];
		
		for(int i=0; i<files.length; i++) {
			File proverFile = files[i];
			ObjectInputStream input = new ObjectInputStream(new FileInputStream(proverFile));
			try {
				AbstractRemoteServer prover = (AbstractRemoteServer) input.readObject();
				toreturn[i] = prover;
			} catch (ClassNotFoundException e) {
				throw new IOException(e);
			}
		}
		return toreturn;
	}

	public static AbstractRemoteServer findByUniqueName(String name) throws IOException  {
		name = name.replace("/", "%2F");
		String fileName = VcProgramDispatchingServerResources.getProperty("remoteProversDirectory");
		if(fileName.endsWith("/")) {
			fileName = fileName+name+"."+VcProgramDispatchingServerResources.getProperty("remoteProversFileExtension"); 
		}
		else {
			fileName = fileName+"/"+name+"."+VcProgramDispatchingServerResources.getProperty("remoteProversFileExtension");
		}
		File proverFile = new File(fileName);
		if(proverFile.exists()) {
			ObjectInputStream input = new ObjectInputStream(new FileInputStream(proverFile));
			try {
				AbstractRemoteServer prover = (AbstractRemoteServer) input.readObject();
				return prover;
			} catch (ClassNotFoundException e) {
				throw new IOException(e);
			}
		}
		else {
			return null;
		}
	}
	
	public static void update(AbstractRemoteServer prover) throws IOException {
		String fileName = VcProgramDispatchingServerResources.getProperty("remoteProversDirectory");
		String name = prover.toString().replace("/", "%2F");
		if(fileName.endsWith("/")) {
			fileName = fileName+name+"."+VcProgramDispatchingServerResources.getProperty("remoteProversFileExtension"); 
		}
		else {
			fileName = fileName+"/"+name+"."+VcProgramDispatchingServerResources.getProperty("remoteProversFileExtension");
		}
		File proverFile = new File(fileName);
		if(!proverFile.exists()) {
			return;
		}
		ObjectOutputStream output = null;
		try {
			output = new ObjectOutputStream(new FileOutputStream(proverFile));
			output.writeObject(prover);
		} catch (IOException e) {
			throw new IOException(e);
		}
		finally {
			if(output != null) {
				output.close();
			}
		}
	}
	
	public static void insert(AbstractRemoteServer prover) throws IOException {
		String fileName = VcProgramDispatchingServerResources.getProperty("remoteProversDirectory");
		String name = prover.toString().replace("/", "%2F");
		if(fileName.endsWith("/")) {
			fileName = fileName+name+"."+VcProgramDispatchingServerResources.getProperty("remoteProversFileExtension"); 
		}
		else {
			fileName = fileName+"/"+name+"."+VcProgramDispatchingServerResources.getProperty("remoteProversFileExtension");
		}
		File proverFile = new File(fileName);
		if(proverFile.exists()) {
			return;
		}
		ObjectOutputStream output = null;
		try {
			output = new ObjectOutputStream(new FileOutputStream(proverFile));
			output.writeObject(prover);
			ServerQueueRegistry.addServer(prover);
		} catch (IOException e) {
			throw new IOException(e);
		} catch (ServerQueueRegistryException e) {
			throw new IOException(e);
		}
		finally {
			if(output != null) {
				output.close();
			}
		}
	}
	
	public static void destroy(AbstractRemoteServer prover) throws IOException {
		String fileName = VcProgramDispatchingServerResources.getProperty("remoteProversDirectory");
		String name = prover.toString().replace("/", "%2F");
		if(fileName.endsWith("/")) {
			fileName = fileName+name+"."+VcProgramDispatchingServerResources.getProperty("remoteProversFileExtension"); 
		}
		else {
			fileName = fileName+"/"+name+"."+VcProgramDispatchingServerResources.getProperty("remoteProversFileExtension");
		}
		File proverFile = new File(fileName);
		if(proverFile.exists()) {
			if(!proverFile.delete()) {
				throw new IOException("Unable to destroy prover!");
			}
			else {
				ServerQueueRegistry.removeServer(prover);
			}
		}
	}

}
