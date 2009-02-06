package org.jmlspecs.jml4.esc.distribution;

import java.lang.management.ManagementFactory;
import java.lang.management.OperatingSystemMXBean;

public class ServerProfile implements IServerProfile {

	/**
	 * 
	 */
	private static final long serialVersionUID = -2672280819523274745L;
	private long committedVirtualMemorySize;
	private int availableProcessors;
	private long freePhysicalMemorySize;
	private long freeSwapSpaceSize;
	private long processCpuTime;
	private double systemLoadAverage;
	private long totalPhysicalMemorySize;
	private int pendingVcs;

	private static long __committedVirtualMemorySize;
	private static int __availableProcessors;
	private static long __freePhysicalMemorySize;
	private static long __freeSwapSpaceSize;
	private static long __processCpuTime;
	private static double __systemLoadAverage;
	private static long __totalPhysicalMemorySize;
	private static int __pendingVcs = 0;

	private static com.sun.management.OperatingSystemMXBean os;

	private static Thread updater;

	static {
		OperatingSystemMXBean osBean = ManagementFactory.getOperatingSystemMXBean();
		os = (com.sun.management.OperatingSystemMXBean) osBean;
		__availableProcessors = os.getAvailableProcessors();
		__totalPhysicalMemorySize = os.getTotalPhysicalMemorySize();
		updater = new Thread() {
			public void run() {
				while(true) {
					__committedVirtualMemorySize = os.getCommittedVirtualMemorySize();
					__freePhysicalMemorySize = os.getFreePhysicalMemorySize();
					__freeSwapSpaceSize = os.getFreeSwapSpaceSize();
					__processCpuTime = os.getProcessCpuTime();
					__systemLoadAverage = os.getSystemLoadAverage();
					try {
						sleep(2500);
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
				}
			}
		};
		updater.setDaemon(true);
		updater.start();
	}

	public ServerProfile() {
		availableProcessors = __availableProcessors;
		totalPhysicalMemorySize = __totalPhysicalMemorySize;
		committedVirtualMemorySize = __committedVirtualMemorySize;
		freePhysicalMemorySize = __freePhysicalMemorySize;
		freeSwapSpaceSize = __freeSwapSpaceSize;
		processCpuTime = __processCpuTime;
		systemLoadAverage = __systemLoadAverage;
		pendingVcs = __pendingVcs;

	}

	@Override
	public synchronized long getCommittedVirtualMemorySize() {
		return committedVirtualMemorySize;
	}

	@Override
	public synchronized int getAvailableProcessors() {
		return availableProcessors;
	}

	@Override
	public synchronized long getFreePhysicalMemorySize() {
		return freePhysicalMemorySize;
	}

	@Override
	public synchronized long getFreeSwapSpaceSize() {
		return freeSwapSpaceSize;
	}

	@Override
	public synchronized long getProcessCpuTime() {
		return processCpuTime;
	}

	@Override
	public synchronized double getSystemLoadAverage() {
		return systemLoadAverage;
	}

	@Override
	public synchronized long getTotalPhysicalMemorySize() {
		return totalPhysicalMemorySize;
	}

	public static synchronized void incrementPending() {
		__pendingVcs++;
	}

	public static synchronized void decrementPending() {
		__pendingVcs--;
	}

	public static synchronized int getPending() {
		return __pendingVcs;
	}

	@Override
	public int getPendingVcs() {
		return pendingVcs;
	}

	public String toString() {
		return 	"Commited Virtual Memory Size: "+ committedVirtualMemorySize + "\n" +
		"Available Processors: " + availableProcessors + "\n" + 
		"Free Physical Memory Size: " + freePhysicalMemorySize + "\n" + 
		"Free Swar Space Size: " + freeSwapSpaceSize + "\n" + 
		"Process CPU Time: " + processCpuTime + "\n" + 
		"System Load Avergae: " + systemLoadAverage + "\n" + 
		"Total Physical Memory Size: " + totalPhysicalMemorySize + "\n" + 
		"Pending VCs: " + pendingVcs + "\n"; 
	}

}
