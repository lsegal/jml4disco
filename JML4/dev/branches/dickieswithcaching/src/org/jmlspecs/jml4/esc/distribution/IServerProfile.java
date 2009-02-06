package org.jmlspecs.jml4.esc.distribution;

import java.io.Serializable;

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
