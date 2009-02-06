package org.jmlspecs.jml4.esc.util;

public class Counter {
	private static int id=0;
	private final int my_id=id++;
	private int count=0;

	public synchronized int getAndIncCounter() {
		int result = ++this.count;
		return result;
	}
	public String toString() {
		return "[Counter("+this.my_id+"): "+this.count+"]"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}
}
