package Dispatcher;
import java.util.ArrayList;
import java.util.HashMap;

import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

import org.jmlspecs.jml4.esc.vc.lang.VC;


public class VCQueue {

	private ArrayList<VC> queue;
	private static HashMap<VC, VcProgram> vcProgMap = new HashMap<VC, VcProgram>();
	private boolean locked;
	
	public VCQueue() {
		queue = new ArrayList<VC>();
		locked = false;
	}
	
	public synchronized VC getNext(){
		if(queue.isEmpty())
			return null;
		return queue.remove(queue.size()-1);
	}
	
	public synchronized void addVC(VC toAdd, VcProgram vcProg){
		queue.add(0, toAdd);
		vcProgMap.put(toAdd, vcProg);
	}
	
	public synchronized void addBalancingVC(VC toAdd) {
		queue.add(0, toAdd);
	}
	
	public static VcProgram getVcProgram(VC vc){
		return vcProgMap.get(vc);
	}
	
	public static void removeVcProgram(VcProgram vcProg){
		VC[] keys = (VC[])vcProgMap.keySet().toArray();
		for(int i=0;i<keys.length;i++)
			if(vcProgMap.get(keys[i]) == vcProg)
				vcProgMap.remove(keys[i]);
	}
	
	public int getSize(){
		return queue.size();
	}
}
