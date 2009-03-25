package org.jmlspecs.jml4.esc.provercoordinator.prover;

import java.util.concurrent.ConcurrentLinkedQueue;

public abstract class ProcessPool {

	protected final int NUM_OF_PROCESSOR = Runtime.getRuntime()
			.availableProcessors();
	private final long TIMEOUT = 10;
	private ConcurrentLinkedQueue idleProcessQueue;
	protected int num_of_process_avaiable = 0;
	protected int MAX_PROCESS = NUM_OF_PROCESSOR * 2;

	
	abstract protected Process createNewProcess();
	abstract protected String launcherCommand();
	abstract public String failedToLaunch();

	protected ProcessPool() {
		idleProcessQueue = new ConcurrentLinkedQueue();
	}

	public void releaseProcess(Process p) {
		idleProcessQueue.add(p);
	}

	/**
	 * poll out on idle process from the queue.  If there's no available 
	 * process, and the number of process created is less than MAXIMUM, create
	 * a new process, otherwise, wait for a process to become free.
	 * @return p:Process
	 */
	public synchronized Process getFreeProcess() {
		Process p = (Process) idleProcessQueue.poll();
		if (p == null) {
			if (num_of_process_avaiable < MAX_PROCESS) {
				p = createNewProcess();
			} else {
				do {
					try {
						Thread.sleep(TIMEOUT);
						p = (Process) idleProcessQueue.poll();
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
				} while(p==null);
			}
		}
		return p;
	}
	
	public int getMAX_PROCESS() {
		return MAX_PROCESS;
	}
	
	public void setMAX_PROCESS(int max_process) {
		
		Process p = (Process) idleProcessQueue.poll();
		while(p != null) {
			p.destroy();
			p = (Process) idleProcessQueue.poll();
		}
		num_of_process_avaiable = 0;
		MAX_PROCESS = max_process;
		
	}
	
	public void notifyDeadProcess(Process p) {
		p.destroy();
		num_of_process_avaiable--;
	}
}
