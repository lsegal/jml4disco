package Dispatcher;

import java.util.ArrayList;

import org.jmlspecs.jml4.esc.vc.lang.VC;

public class LoadBalancerThread extends Thread {

	private static ArrayList<VCQueue> queues;
	private static ArrayList<VC> toBeAllocated;
	
	public LoadBalancerThread(ArrayList<VCQueue> queues) {
		this.queues = queues;
		toBeAllocated = new ArrayList<VC>();
	}
	
	public void run() {
		int count = 30000;
		while(count-- > 0){
			int sum = 0;
			int index = 0;
			int[] nums = new int[queues.size()];
			
			for(VCQueue q:queues){
				VC vc = q.getNext();
				if(vc != null)
					toBeAllocated.add(vc);
				nums[index] = q.getSize();
				if(nums[index] == 0 && toBeAllocated.size() > 0)
					q.addBalancingVC(toBeAllocated.remove(0));
				sum += nums[index++];
			}
			int avg = sum/queues.size() + 1;
			index=0;
			for(VCQueue q:queues){
				int diff = nums[index++] - avg;
				for(int i=0;i<diff && toBeAllocated.size() > 0;i++)
					q.addBalancingVC(toBeAllocated.remove(0));
			}
			try {
				sleep(3);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		System.out.println("BALANCING QUEUE DIED");
	}
}
