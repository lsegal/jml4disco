package org.jmlspecs.jml4.esc.gc.lang;

import java.util.ArrayList;
import java.util.List;

/**
 * Provides an enumeration of the kinds of assertions that can be
 * thrown in JML code.
 */
public class KindOfAssertion {

	//* a cache of all the kinds, initialized on the first call to all()
	private static /*@nullable*/ KindOfAssertion[] allCache = null;

	//* a list to hold of all the kinds
	private static final List all = new ArrayList();

	//* inline assert
	public static final KindOfAssertion ASSERT = new KindOfAssertion("Assert"); //$NON-NLS-1$

	//* method precondition (when method is called)
	public static final KindOfAssertion PRE = new KindOfAssertion("Precondition"); //$NON-NLS-1$

	//* method postcondition (when method returns)
	public static final KindOfAssertion POST = new KindOfAssertion("Postcondition"); //$NON-NLS-1$

	//* loop variant (when expression doesn't decrease)
	public static final KindOfAssertion LOOP_VAR = new KindOfAssertion("LoopVariant"); //$NON-NLS-1$

	//* loop invariant
	public static final KindOfAssertion LOOP_INVAR_PRE = new KindOfAssertion("LoopInvariant_before"); //$NON-NLS-1$
	public static final KindOfAssertion LOOP_INVAR = new KindOfAssertion("LoopInvariant"); //$NON-NLS-1$

	//* class or instance invariant
	public static final KindOfAssertion INVARIANT = new KindOfAssertion("Invariant"); //$NON-NLS-1$

	public static final KindOfAssertion UNKNOWN = new KindOfAssertion("Unknown"); //$NON-NLS-1$

	//* a textual representation of the kind of assertion
	public final String description;

	/**
	 * creates a new kind of assertion with the given description
	 * 
	 * @param description a textual representation of the kind of assertion
	 */
	private KindOfAssertion(String description) {
		this.description = description;
		all.add(this);
	}

	public String toString() {
		return this.description;
	}

	public static synchronized KindOfAssertion[] all() {
		if (allCache == null) {
			allCache = (KindOfAssertion[]) all.toArray(new KindOfAssertion[0]);
		}
		return allCache;
	}

	public static boolean matches(String label) {
		if (allCache==null) 
			all();
		for (int i = 0; i < allCache.length; i++) {
			if (allCache[i].description.equals(label))
				return true;
		}
		return false;
	}

	public static /*@nullable*/ KindOfAssertion fromString(String labelName) {
		KindOfAssertion[] a = all();
		for (int i = 0; i < a.length; i++) {
			if (a[i].description.equals(labelName))
				return a[i];
		}
		return null;
	}

}
