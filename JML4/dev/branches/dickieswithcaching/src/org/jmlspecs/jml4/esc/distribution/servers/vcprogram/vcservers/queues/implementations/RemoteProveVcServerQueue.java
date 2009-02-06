package org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.implementations;

import java.util.Collection;
import java.util.Iterator;
import java.util.PriorityQueue;
import java.util.Queue;

import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.RemoteProveVcServer;
import org.jmlspecs.jml4.esc.distribution.servers.vcprogram.vcservers.queues.implementations.comparator.RemoteProveVcServerComparator;

public class RemoteProveVcServerQueue implements Queue<RemoteProveVcServer> {

	private PriorityQueue<RemoteProveVcServer> queue;
	private RemoteProveVcServerComparator comparator;
	
	public RemoteProveVcServerQueue(int initialCapacity) {
		comparator = new RemoteProveVcServerComparator();
		queue = new PriorityQueue<RemoteProveVcServer>(initialCapacity, comparator);
	}

	@Override
	public boolean add(RemoteProveVcServer arg0) {
		return queue.add(arg0);
	}

	@Override
	public RemoteProveVcServer element() {
		return queue.element();
	}

	@Override
	public boolean offer(RemoteProveVcServer arg0) {
		return queue.offer(arg0);
	}

	@Override
	public RemoteProveVcServer peek() {
		return queue.peek();
	}

	@Override
	public RemoteProveVcServer poll() {
		return queue.poll();
	}

	@Override
	public RemoteProveVcServer remove() {
		return queue.remove();
	}

	@Override
	public boolean addAll(Collection<? extends RemoteProveVcServer> arg0) {
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
	public Iterator<RemoteProveVcServer> iterator() {
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
