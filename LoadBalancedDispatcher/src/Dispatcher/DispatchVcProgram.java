package Dispatcher;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Vector;

import org.jmlspecs.jml4.esc.Esc;
import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcDistributed;
import org.jmlspecs.jml4.esc.result.lang.Result;
import org.jmlspecs.jml4.esc.vc.lang.VC;
import org.jmlspecs.jml4.esc.vc.lang.VcProgram;

public class DispatchVcProgram {

	private static int totalVCcount;
	private static int currentVCcount;
	private static ArrayList<VCQueue> queues;
	private static ArrayList<VCDispatcherThread> threads;
	private static ArrayList<int[]> done;
	private static ArrayList<ArrayList<Result>> accumulators;
	private static HashMap<VcProgram, Integer> indexOfProgram;

	private static int numofservers = Integer.parseInt(VCDispatcherThread
			.getUrlString("numofservers"));

	public Result[] dispatchVcProgram(final VcProgram vcProg) {
		try{		
			if (totalVCcount == 0)
				createQueues();
			populateQueues(vcProg);
			while(getDone(vcProg)[0] != vcProg.getAsImplications().length){
				//DO NOTHING
				Thread.sleep(10);
			}
	
			Esc.waitForItToFinish(getDone(vcProg), vcProg.getAsImplications().length);
			   if (getAccumulator(vcProg).size() == 0)
				   getAccumulator(vcProg).add(Result.VALID[0]);
		} catch(Exception e){
			e.printStackTrace();
		}
		   return (Result[])getAccumulator(vcProg).toArray(Result.EMPTY);
	}

	public synchronized void createQueues() {
		
		if(totalVCcount == 0)
		{
			totalVCcount = 1;
			currentVCcount = 1;
			queues = new ArrayList<VCQueue>();
			threads = new ArrayList<VCDispatcherThread>();
			done = new ArrayList<int[]>();
			accumulators = new ArrayList<ArrayList<Result>>();
			indexOfProgram = new HashMap<VcProgram, Integer>();
			for (int i = 0; i < numofservers; i++)
				queues.add(new VCQueue());
			int count = 0;
			for (VCQueue q : queues) {
				VCDispatcherThread thread = new VCDispatcherThread(count++
						% numofservers + 1, q);
				thread.start();
				threads.add(thread);
			}
			LoadBalancerThread loadBalancer = new LoadBalancerThread(queues);
			loadBalancer.start();
		}
	}

	public void populateQueues(final VcProgram vcProg) {
		final VC[] vcs = vcProg.getAsImplications();
		if (Esc.GEN_STATS)
			System.out
					.println("ESC4\tProveVcProgram\tloop\tstart\t" + vcProg.methodIndicator + "\t" + Esc.timeDelta()); //$NON-NLS-1$ //$NON-NLS-2$
		for (int i = 0; i < vcs.length; i++) {
			queues.get(i % queues.size()).addVC(vcs[i], vcProg);
			vcs[i].setName(vcProg.methodIndicator + "_" + (i + 1)); //$NON-NLS-1$	  
		}
		//These four lines need to be synchronizeed together
		method1(vcProg);
	}
	
	public synchronized static void method1(final VcProgram vcProg){
		done.add(new int[1]);
		accumulators.add(new ArrayList<Result>());
		indexOfProgram.put(vcProg, totalVCcount);
		totalVCcount++;
	}
	
	public static ArrayList<Result> getAccumulator(
			VcProgram vcProgram) {
		return accumulators.get( indexOfProgram.get(vcProgram) - 1 );
	}

	public static int[] getDone(VcProgram vcProgram) {
		return done.get( indexOfProgram.get(vcProgram) - 1 );
	}

	public synchronized static void incrementDone(VcProgram vcProgram) {
		done.get(indexOfProgram.get(vcProgram) - 1)[0]++;
	}
}
