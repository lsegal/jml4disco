package org.jmlspecs.jml4.esc.distribution.servers.vcprogram;

import java.util.ArrayList;
import java.util.HashMap;

import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;


public class VcCache {
	
	private static HashMap<VC, Result[]> cache = new HashMap<VC, Result[]>();
	private static ArrayList<VC> LRU = new ArrayList<VC>();
	private static ArrayList<VC> simplifyList = new ArrayList<VC>();
	private static ArrayList<VC> cvc3List = new ArrayList<VC>();
	private static ArrayList<VC> notSimplifyList = new ArrayList<VC>();

	private VcCache(){}
	
	public synchronized static Result[] get(VC vc){
		if(cache.containsKey(vc)){
			Result[] toReturn = cache.get(vc);
			int pos = LRU.indexOf(vc);
			LRU.remove(pos);
			LRU.add(vc);
			return toReturn;
		}
		return null;
			
	}

	public synchronized static void add(VC vc, Result[] result, String prover){
		if(cache.size() > 1000000) {
			if(simplifyList.size() > 0){
				VC toRemove = simplifyList.remove(0);
				removeVcFromCache(toRemove);
			}
			else if(cvc3List.size() > 0){
				VC toRemove = cvc3List.remove(0);
				removeVcFromCache(toRemove);
			}
			else if(notSimplifyList.size() > 0){
				VC toRemove = notSimplifyList.remove(0);
				removeVcFromCache(toRemove);
			}
			else {
				VC toRemove = LRU.get(0);
				removeVcFromCache(toRemove);
			}
			cache.put(vc, result);
			LRU.add(vc);
		}
		if(prover.equals("simplify")){
			simplifyList.add(vc);
		}
		else if(prover.equals("cvc3")){
			cvc3List.add(vc);
		}
		else if(prover.equals("notsimplify")){
			notSimplifyList.add(vc);
		}
		LRU.add(vc);
		cache.put(vc, result);
	}

	private synchronized static void removeVcFromCache(VC toRemove) {
		cache.remove(toRemove);
		int pos = LRU.indexOf(toRemove);
		LRU.remove(pos);
	}
}