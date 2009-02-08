package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers;

import java.net.MalformedURLException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.implementations.RemoteTomCatServer;

public class ServerMapper {

	private static final String PROPERTIES_FILE = "jml4-disco-dispatcher"; // To initialize
	
	private static HashMap<String, AbstractRemoteServer> servers = init();
	
	private static synchronized HashMap<String, AbstractRemoteServer> init() {
		if(servers!=null) {
			return servers;
		}
		try {
			ResourceBundle bundle = ResourceBundle.getBundle(PROPERTIES_FILE);

			// TODO check that numberOfServers key exists
			int numberOfServers = Integer.parseInt(bundle
					.getString("numberOfServers"));
			HashMap<String, AbstractRemoteServer> newqueue = new HashMap<String, AbstractRemoteServer>(numberOfServers);

			for (int i = 1; i <= numberOfServers; i++) {
				String serverInfo = bundle.getString("proverServer." + i);
				try {
					newqueue.put(serverInfo, new RemoteTomCatServer(serverInfo));
				}
				catch(MalformedURLException e) {
					System.out.println("Unable to add server '"+serverInfo+"'");
					e.printStackTrace();
				}
			}
			return newqueue;
		} catch (MissingResourceException e) {
			e.printStackTrace();
		}
		return null;
	}
	
	public static List<AbstractRemoteServer> findAll() {
		return new ArrayList<AbstractRemoteServer>(servers.values());
	}
	
	public static AbstractRemoteServer findByServerInfo(String info) {
		return servers.get(info);
	}
	
}
