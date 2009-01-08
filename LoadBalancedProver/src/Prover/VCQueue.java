package Prover;
import java.util.ArrayList;

import org.jmlspecs.jml4.esc.vc.lang.VC;


public class VCQueue {

	private ArrayList<VC> queue;
	
	public VCQueue() {
		queue = new ArrayList<VC>();
	}
	
	public VC getNext(){
		return queue.remove(queue.size()-1);
	}
	
	public boolean hasNext(){
		if(queue.size() > 0)
			return true;
		return false;
	}
	
	public void addVC(VC toAdd){
		queue.add(0, toAdd);
	}
}
