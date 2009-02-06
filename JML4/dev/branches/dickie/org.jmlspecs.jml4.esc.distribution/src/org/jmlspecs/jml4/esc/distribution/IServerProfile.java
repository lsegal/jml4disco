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
