package org.jmlspecs.jml4.esc.gc;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import org.jmlspecs.jml4.esc.gc.lang.simple.expr.SimpleAssignable;
import org.jmlspecs.jml4.esc.util.Utils;

public class IncarnationMap  {

	private final HashMap/*<SimpleAssignable, Set<Integer>>*/ map = new HashMap/*<SimpleAssignable, Set<Integer>>*/();

	public IncarnationMap() {
		/*empty*/
	}
	
	public void clear() {
		this.map.clear();
	}

	public boolean containsKey(SimpleAssignable key) {
		return this.map.containsKey(key);
	}

	private static Integer asValue(int value) {
		return Utils.valueOf(value);
	}

	public Set entrySet() {
		return this.map.entrySet();
	}

	public Set/*<Integer>*/ get(SimpleAssignable key) {
		Set/*<Integer>*/ set = (Set/*<Integer>*/ ) this.map.get(key);
		if (set == null) {
			set = new HashSet/*<Integer>*/();
			this.map.put(key, set);
		}
		return set;
	}

	public int getMax(SimpleAssignable key) {
		Set/*<Integer>*/ set = (Set/*<Integer>*/ ) this.map.get(key);
		if (set == null) {
			set = new HashSet/*<Integer>*/();
			set.add(asValue(0));
			this.map.put(key, set);
		}
		return Utils.max(set);
	}

	public boolean isEmpty() {
		return this.map.isEmpty();
	}

	public Set keySet() {
		return this.map.keySet();
	}

	public void put(SimpleAssignable key, Set/*<Integer>*/ value) {
		this.map.put(key, value);
	}

	public void put(SimpleAssignable key, int value) {
		Utils.assertTrue(value >= 0, "value is negative"); //$NON-NLS-1$
		Set/*<Integer>*/ values = new HashSet/*<Integer>*/();
		values.add(asValue(value));
		this.map.put(key, values);
		Utils.assertTrue(((Set)map.get(key)).size() == 1, "size not correct"); //$NON-NLS-1$
	}

	public void add(SimpleAssignable key, int value) {
		Utils.assertTrue(value >= 0, "value is negative"); //$NON-NLS-1$
		int old_size = (this.containsKey(key) ? ((Set)map.get(key)).size() : 0);
		Set/*<Integer>*/ values = this.get(key);
		values.add(asValue(value));
		int diff = ((Set)map.get(key)).size() - old_size; 
		Utils.assertTrue(diff == 0 || diff == 1, "size not correct"); //$NON-NLS-1$
		Utils.assertTrue(old_size != 0 || diff == 1, "size not correct"); //$NON-NLS-1$
	}

	public void remove(SimpleAssignable key) {
		this.map.remove(key);
	}

	public int size() {
		return this.map.size();
	}
	public String toString() {
		return this.map.toString();
	}

	public Map/*<String var, Integer>*/ toStringIntegerMap() {
		Entry[] entries = (Entry[])this.entrySet().toArray(new Entry[0]);
		Map/*<String var, Integer>*/ result = new HashMap/*<String var, Integer>*/();
		for (int i = 0; i < entries.length; i++) {
			Entry entry = entries[i];
			SimpleAssignable key = (SimpleAssignable) entry.getKey();
			Set value = (Set/*<Integer>*/)entry.getValue();
			int max = Utils.max(value);
			result.put(key.getName(), Utils.valueOf(max));
		}
		return result;
	}
	
	public IncarnationMap copy() {
		IncarnationMap result = new IncarnationMap();
		for (Iterator i = this.map.keySet().iterator(); i.hasNext();) {
			SimpleAssignable var = (SimpleAssignable) i.next();
			Set/*<Integer>*/ value = this.get(var);
			for (Iterator j = value.iterator(); j.hasNext();) {
				Integer inc = (Integer) j.next();
				int incarnation = inc.intValue();
				result.add(var, incarnation);
			}
		}
		return result;
	}
	
}
