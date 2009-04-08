/*
 * IServerProfile
 * 
 * Version 2.0 
 *
 * January 28th, 2009
 * 
 * Contributors:
 * CJ Sheu, R Le Guen
 */
package org.jmlspecs.jml4.esc.distribution;

import java.io.Serializable;

/**
 * This interface defines the various data that should be collected as a server
 * profile.
 */
public interface IServerProfile extends Serializable {

	public long getCommittedVirtualMemorySize();

	public int getAvailableProcessors();

	public long getFreePhysicalMemorySize();

	public long getFreeSwapSpaceSize();

	public long getProcessCpuTime();

	public double getSystemLoadAverage();

	public long getTotalPhysicalMemorySize();

	public int getPendingVcs();

}
