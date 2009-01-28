/*
 * ServerQueue
 * 
 * Version 2.0 
 *
 * January 28th, 2009
 * 
 * Contributors:
 * R Le Guen, N Grigoropoulos
 */
package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues;

import java.util.Collection;
import java.util.Iterator;
import java.util.PriorityQueue;
import java.util.Queue;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.AbstractRemoteServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.comparator.ServerComparator;

/**
 * This class serves as a queue of servers which will re-sort itself whenever
 * the head element is viewed.
 * 
 */
public class ServerQueue implements Queue<AbstractRemoteServer> {

	private PriorityQueue<AbstractRemoteServer> queue;
	private ServerComparator comparator; // Will determine which server is

	// "better" than another

	/**
	 * @param initialCapacity
	 *            The initial maximum number of servers to be stored.
	 */
	public ServerQueue(int initialCapacity) {
		comparator = new ServerComparator();
		queue = new PriorityQueue<AbstractRemoteServer>(initialCapacity,
				comparator);
	}

	// --------- Overridden methods from Queue ---------
	@Override
	public boolean add(AbstractRemoteServer arg0) {
		return queue.add(arg0);
	}

	@Override
	public AbstractRemoteServer element() {
		return queue.element();
	}

	@Override
	public boolean offer(AbstractRemoteServer arg0) {
		return queue.offer(arg0);
	}

	/**
	 * Looks at the top-most element in the queue without removing it Will cause
	 * the queue to re-sort itself.
	 * 
	 * @return The "best" server to dispatch to.
	 */
	@Override
	public synchronized AbstractRemoteServer peek() {
		AbstractRemoteServer toReturn = queue.remove();
		// Here the head is temporarily removed and replaced, causing the
		// Priority Queue to resort itself.
		queue.add(toReturn);
		return toReturn;
	}

	@Override
	public AbstractRemoteServer poll() {
		return queue.poll();
	}

	@Override
	public AbstractRemoteServer remove() {
		return queue.remove();
	}

	@Override
	public boolean addAll(Collection<? extends AbstractRemoteServer> arg0) {
		return queue.addAll(arg0);
	}

	@Override
	public void clear() {
		queue.clear();
	}

	@Override
	public boolean contains(Object arg0) {
		return queue.contains(arg0);
	}

	@Override
	public boolean containsAll(Collection<?> arg0) {
		return queue.containsAll(arg0);
	}

	@Override
	public boolean isEmpty() {
		return queue.isEmpty();
	}

	@Override
	public Iterator<AbstractRemoteServer> iterator() {
		return queue.iterator();
	}

	@Override
	public boolean remove(Object arg0) {
		return queue.remove(arg0);
	}

	@Override
	public boolean removeAll(Collection<?> arg0) {
		return queue.removeAll(arg0);
	}

	@Override
	public boolean retainAll(Collection<?> arg0) {
		return queue.retainAll(arg0);
	}

	@Override
	public int size() {
		return queue.size();
	}

	@Override
	public Object[] toArray() {
		return queue.toArray();
	}

	@Override
	public <T> T[] toArray(T[] arg0) {
		return queue.toArray(arg0);
	}

}
