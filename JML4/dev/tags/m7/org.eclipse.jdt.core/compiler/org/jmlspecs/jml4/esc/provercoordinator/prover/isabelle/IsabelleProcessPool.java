package org.jmlspecs.jml4.esc.provercoordinator.prover.isabelle;

import java.io.File;
import java.io.IOException;

import org.jmlspecs.jml4.esc.provercoordinator.prover.ProcessPool;
import org.jmlspecs.jml4.util.Logger;

/**
 * Singleton
 * Theorem Prove Isabelle ESC4 Process pool implementation
 */
public class IsabelleProcessPool extends ProcessPool {

	private static IsabelleProcessPool self;
	private static final String ISABELLE_CMD = "isabelle -I ESC4"; //$NON-NLS-1$
	private static final String OS_NAME_KEY = "os.name"; //$NON-NLS-1$
	private static final String OS_LINUX = "Linux"; //$NON-NLS-1$
	private static final boolean DEBUG = false;

	private IsabelleProcessPool() {
		super();
		Process p = createNewProcess();
		releaseProcess(p);
	}

	synchronized public static IsabelleProcessPool getInstance() {
		if (self == null) {
			self = new IsabelleProcessPool();
		}
		return self;
	}

	public String launcherCommand() {
		String osName = System.getProperty(OS_NAME_KEY);
		//right now, we check only for linux os
		if(osName.equals(OS_LINUX)) {
			return File.separatorChar == '/' ? ISABELLE_CMD
					: "bash /usr/local/bin/" + ISABELLE_CMD; //$NON-NLS-1$
		}
		return "";  //$NON-NLS-1$
	}
	
	public String failedToLaunch() {
		return "failed to launch " + launcherCommand(); //$NON-NLS-1$
	}
	
	
	/* (non-Javadoc)
	 * @see org.jmlspecs.jml4.esc.provercoordinator.prover.ProcessPool#createNewProcess()
	 */
	protected Process createNewProcess() {
		try {
			Process process = Runtime.getRuntime().exec(launcherCommand());
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
