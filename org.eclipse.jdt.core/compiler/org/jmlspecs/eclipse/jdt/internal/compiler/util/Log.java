/*
 * This file is part of the JML-ESC plugin project.
 * @author David Cok
 * 
 * Created on Aug 26, 2004
 */
package org.jmlspecs.eclipse.jdt.internal.compiler.util;

import java.io.PrintStream;

/**
 * This class provides a uniform interface for logging informational
 * and error messages.  Do not use it for messages to the user in the
 * course of normal interaction with the tool.  Instead, the 
 * informational output is for debugging and tracing purposes; the
 * error output is for internal error reporting (and not, for
 * example, for reports to users about erroneous user input).
 * <P>
 * Log.on is a boolean flag to be used in user code as a convenience
 * test, as in  <BR>
 *        if (Log.on) Log.log(msg);  <BR>
 * The test happens before the method call.

 *
 * Note that output sent to System.out may be lost depending on
 * the manner in which Eclipse is started (it might also end up
 * in a command terminal or in a parent Console during plugin
 * development).
 * 
 */
public class Log {
    
	/** Holds a current value for the log object, for convenience */
	/*@ non_null */ public static Log log = new Log();

	/** A flag used to record whether or not to output tracing 
	 *  information.
	 */
	public static boolean on = false;
	
	public Log() {}

	/**
	 * Initializes any internal state of the log, e.g. based on
	 * stored preferences or properties.
	 * 
	 * @param on Sets (globally) whether anything is desired to be logged or not.
	 * 			This is simply to be tested in code prior to calling log() or errorlog(),
	 * 			to avoid the method invocation when logging is off, as in
	 * 				if (Log.on) Log.log(msg);
	 */
	//@ requires log != null;
	//@ modifies Log.on, log.useConsole, log.alsoLogInfo;
	//@ ensures Log.on == on;
	//@ ensures log.useConsole == useConsole;
	//@ ensures log.alsoLogInfo == alsoLogInfo;
	public static void initializeState(boolean on) {
		boolean b = Log.on;
		Log.on = on;
		if (log == null) {
			// Internal error - no log yet defined
			// FIXME
			return;
		}
		if (b != Log.on) Log.log("Logging is now " +
				(Log.on ? "on" : "off"));
	}
	
	/**
	 * Records an informational message to the current log
	 * @param msg The message to log
	 */
	//@ requires msg != null;
	//@ modifies log.content;
	public static void log(String msg) { if (Log.on) log.ilog(msg); }
	
    /**
     * Records an error message to the current log
     * @param msg The message to log
     * @param e An associated exception (may be null)
     */
    //@ requires msg != null;   
    //@ modifies log.content;
    public static void errorlog(String msg, Throwable e) {
        if (Log.on) log.ierrorlog(msg,e);
    }
    
    /**
     * Records an informational message to the current log
     * @param msg The message to log
     * @param e An associated exception (may be null)
     */
    //@ requires msg != null;   
    //@ modifies log.content;
    public void ilog(String msg) {
        System.out.println(msg);
    }

    /**
     * Records an error message to the current log
     * @param msg The message to log
     * @param e An associated exception (may be null)
     */
    //@ requires msg != null;   
    //@ modifies log.content;
    public void ierrorlog(String msg, Throwable e) {
//        System.err.println(msg + " " + e);
        // We use System.out instead of System.err because otherwise
        // it seemed the output was not flushed/interleaved correctly
        // Perhaps some flushing would help ?? FIXME
        System.out.println(msg);
        if (e != null) e.printStackTrace(System.out);

    }
    

	/**
	 * Creates a PrintStream that, when written to, writes to the Eclipse Console
	 * of the current log object
	 * 
	 * @return a PrintStream connected to the Eclipse Console
	 */
	//@ requires log != null;
	//@ pure
	public static PrintStream logPrintStream() {
		return System.out;
	}

}

