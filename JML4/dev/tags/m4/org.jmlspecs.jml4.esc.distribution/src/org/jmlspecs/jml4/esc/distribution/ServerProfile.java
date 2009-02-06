package org.jmlspecs.jml4.esc.distribution;

import java.lang.management.ManagementFactory;
import java.lang.management.OperatingSystemMXBean;

/**
 * The Server Profile is a helper class for the performance data being retrieved
 * from remote servers.
 */
public class ServerProfile implements IServerProfile {

	/**
	 * Each server profile has a number of private attributes which are
	 * initialized to the data provided by the operating system.
	 * 
	 * This essentially means that the data is first gathered statically by a
	 * thread and when the server profile is called, the most up-to-date data is
	 * then copied to a ServerProfile instance which is then sent back to the
	 * dispatcher.
	 */

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
		OperatingSystemMXBean osBean = ManagementFactory
				.getOperatingSystemMXBean();
		os = (com.sun.management.OperatingSystemMXBean) osBean;
		__availableProcessors = os.getAvailableProcessors();
		__totalPhysicalMemorySize = os.getTotalPhysicalMemorySize();
		updater = new Thread() {
			public void run() {
				while (true) {
					__committedVirtualMemorySize = os
							.getCommittedVirtualMemorySize();
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

	/**
	 * @returns The committed virtual memory of the server.
	 */
	@Override
	public synchronized long getCommittedVirtualMemorySize() {
		return committedVirtualMemorySize;
	}

	/**
	 * @returns The number of available processors of the server.
	 */
	@Override
	public synchronized int getAvailableProcessors() {
		return availableProcessors;
	}

	/**
	 * @returns The amount of free physical memory of the server.
	 */
	@Override
	public synchronized long getFreePhysicalMemorySize() {
		return freePhysicalMemorySize;
	}

	/**
	 * @returns The amount of free swap space remaining in the server.
	 */
	@Override
	public synchronized long getFreeSwapSpaceSize() {
		return freeSwapSpaceSize;
	}

	/**
	 * @returns The amount of time the process spent in the server's CPU.
	 */
	@Override
	public synchronized long getProcessCpuTime() {
		return processCpuTime;
	}

	/**
	 * @returns The average system load of the server.
	 */
	@Override
	public synchronized double getSystemLoadAverage() {
		return systemLoadAverage;
	}

	/**
	 * @returns The total amount of physical memory of the server.
	 */
	@Override
	public synchronized long getTotalPhysicalMemorySize() {
		return totalPhysicalMemorySize;
	}

	/**
	 * Increments the number of VC's pending on the server by one.
	 */
	public static synchronized void incrementPending() {
		__pendingVcs++;
	}

	/**
	 * Decrements the number of VC's pending on the server by one.
	 */
	public static synchronized void decrementPending() {
		__pendingVcs--;
	}

	/**
	 * @return The number of pending VC's.
	 */
	public static synchronized int getPending() {
		return __pendingVcs;
	}

	/**
	 * @return The number of pending VC's.
	 */
	@Override
	public int getPendingVcs() {
		return pendingVcs;
	}

	public String toString() {
		return "Commited Virtual Memory Size: " + committedVirtualMemorySize
				+ "\n" + "Available Processors: " + availableProcessors + "\n"
				+ "Free Physical Memory Size: " + freePhysicalMemorySize + "\n"
				+ "Free Swar Space Size: " + freeSwapSpaceSize + "\n"
				+ "Process CPU Time: " + processCpuTime + "\n"
				+ "System Load Avergae: " + systemLoadAverage + "\n"
				+ "Total Physical Memory Size: " + totalPhysicalMemorySize
				+ "\n" + "Pending VCs: " + pendingVcs + "\n";
	}
}
