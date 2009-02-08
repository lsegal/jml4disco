/*
 * ServerComparator
 * 
 * Version 2.0 
 *
 * January 28th, 2009
 * 
 * Contributors:
 * R Le Guen, N Grigoropoulos
 */
package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.comparator;

import java.util.Comparator;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;

/**
 * This class serves as a comparator for servers in order to determine which
 * server is more desirable for dispatching VC's to.
 * 
 */
public class ServerComparator implements Comparator<AbstractRemoteServer> {
	/**
	 * @param firstServer
	 *            The comparing is done relative to this server.
	 * @param serverToCompare
	 *            The server to compare with the first server.
	 * @return will return a positive value if the first server is more
	 *         desirable than the second.
	 */
	public int compare(AbstractRemoteServer firstServer,
			AbstractRemoteServer serverToCompare) {
/*
		double firstServerSystemLoadAverage = firstServer
				.getSystemLoadAverage();
		double secondServerSystemLoadAverage = serverToCompare
				.getSystemLoadAverage();

		if (firstServerSystemLoadAverage < 0
				&& secondServerSystemLoadAverage < 0) {
			return 0;
		}

		if (firstServerSystemLoadAverage == 0) {
			firstServerSystemLoadAverage = 0.000001;
		}
		if (secondServerSystemLoadAverage == 0) {
			secondServerSystemLoadAverage = 0.000001;
		}

		int toReturn = (int) ((double) (firstServer.getPendingVcs() * 100) / firstServerSystemLoadAverage)
				- (int) ((double) (serverToCompare.getPendingVcs() * 100) / secondServerSystemLoadAverage);
		
		if(Math.abs(toReturn)>5) {
			return toReturn;
		}
		else {*/
			int timingdiff = (int) (firstServer.timeSinceLastProve()-serverToCompare.timeSinceLastProve());
			return timingdiff;
/*		}*/
	}

}
