package org.jmlspecs.jml4.esc.provercoordinator.prover.simplify;

import java.io.IOException;
import java.io.OutputStream;

import org.jmlspecs.jml4.esc.provercoordinator.prover.ProcessPool;
import org.jmlspecs.jml4.util.Logger;

/**
 * Singleton
 * Simplify Theorem Prover process pool implementation
 */
public class SimplifyProcessPool extends ProcessPool {

	private static final String  SIMPLIFY = "simplify";//"gnome-terminal --command simplify"; //$NON-NLS-1$
	private static final String OS_NAME_KEY = "os.name"; //$NON-NLS-1$
	private static final String OS_LINUX = "Linux"; //$NON-NLS-1$
	private static final boolean DEBUG = false;
	private static SimplifyProcessPool self;


	private SimplifyProcessPool() {
		super();
		Process p = createNewProcess();  //by default, one process will be created
		releaseProcess(p);
	}

	synchronized public static SimplifyProcessPool getInstance() {
		if (self == null) {
			self = new SimplifyProcessPool();
		}
		return self;
	}

	public String launcherCommand() {
		String osName = System.getProperty(OS_NAME_KEY);
		//check only for linux os type for the moment
		if(osName.equals(OS_LINUX)) {
			return SIMPLIFY;
		}
		return ""; //$NON-NLS-1$
	}
	
	public String failedToLaunch() {
		return "failed to launch " + launcherCommand(); //$NON-NLS-1$
	}
	
	protected Process createNewProcess() {
		try {
			Process process = Runtime.getRuntime().exec(launcherCommand());
			String ubp = SimplifyBackgroundPredicate.get();
			OutputStream out = process.getOutputStream();
			out.write(ubp.getBytes());
			out.flush();
			num_of_process_avaiable++;
			return process;
		} catch (IOException e) {
			System.err.println(e);
			if (DEBUG) {
				Logger.print(failedToLaunch());
				Logger.print(e.toString());
			}
		} catch (SecurityException e) {
			if (DEBUG) {
				Logger.print(failedToLaunch());
				Logger.print(e.toString());
			}
		}
		return null;
	}
}
