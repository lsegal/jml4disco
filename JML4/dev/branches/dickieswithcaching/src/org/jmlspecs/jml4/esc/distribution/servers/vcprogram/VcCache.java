package org.jmlspecs.jml4.esc.distribution.servers.vcprogram;

import java.util.HashMap;

import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;

public class VcCache {

	private static VcCache cacheLink;
	private static HashMap<VC, Result[]> cache = new HashMap<VC, Result[]>();
		
	private VcCache(){}
	
	public static VcCache getInstance(){
		if(cacheLink == null)
			cacheLink = new VcCache();
		return cacheLink;
	}
	
	public boolean contains(VC tocheck){
		if(cache.containsKey(tocheck))
			return true;
		return false;
	}
	
	public Result[] get(VC toget){
		if(cache.containsKey(toget))
			return cache.get(toget);
		return null;
	}
	
	public void put(VC toadd, Result[] result){
		cache.put(toadd, result);
	}
}
