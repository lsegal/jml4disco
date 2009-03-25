package org.jmlspecs.jml4.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Date;

public class Logger {
   private static final boolean DEBUG   = false;
   private static final boolean TO_OUT  = true;
   private static final boolean TO_FILE = true; 

   private static final String filename = System.getProperty("user.home") +  //$NON-NLS-1$
   										  System.getProperty("file.separator") + //$NON-NLS-1$ 
   										  "jml4.log";   //$NON-NLS-1$
   private static final Logger logger = new Logger();
   private static final int MAX_BUFFER_LEN = 0;
   private final StringBuffer buffer = new StringBuffer();
   
   static {
	   if (DEBUG) {
	       File file = new File(filename);
	       if (file.exists())
	    	   file.delete();
	       println("***** "+(new Date()).toString()+" *****"); //$NON-NLS-1$ //$NON-NLS-2$
	   }
   }

   //@ requires false;
   public static void println(String msg) {
	   if (DEBUG)
		   logger.local_print(msg+"\n"); //$NON-NLS-1$
   }

   //@ requires false;
   public static void print(String msg) {
	   if (DEBUG)
		   logger.local_print(msg);
   }

   //@ requires false;
   public static void dumpStack() {
	   if (DEBUG)
		   logger.local_dumpStack();
   }
   
   //@ requires false;
   public static void dumpStack(Throwable t) {
	   if (DEBUG)
		   logger.local_dumpStack(t);
   }

   //@ requires false;
   public static void flush() {
	   if (DEBUG)
		   logger.local_flush();
   }
   //@ requires false;
   private void local_print(String msg) {
	  if (TO_OUT)
		  System.out.print(msg);
	  if (TO_FILE) {
		  this.buffer.append(msg);
		  if (this.buffer.length() > MAX_BUFFER_LEN)
			  local_flush();
	  }
   }

   //@ requires false;
   public void local_dumpStack() {
	   local_dumpStack(new Exception("Debugging stack dump")); //$NON-NLS-1$
   }
   
   //@ requires false;
   public void local_dumpStack(Throwable t) {
	   StringWriter sOut = new StringWriter();
	   PrintWriter out = new PrintWriter(sOut);
	   if (TO_OUT)
		   t.printStackTrace(out);
	   if (TO_FILE)
		   local_print(sOut.toString());
   }

   //@ requires false;
   private void local_flush() {
	  if (this.buffer.length() > 0) {
	      PrintWriter out=open();
	      if (out != null) {
		      out.print(this.buffer.toString());
		      out.close();
	      }
	      this.buffer.setLength(0);
	  }
   }

   //@ requires false;
   private static PrintWriter open() {
      PrintWriter result = null;
      try {
    	  result = new PrintWriter(new FileOutputStream(filename, true));
      } catch (IOException e) { 
    	  throw new RuntimeException(e);
      }
      return result;
   }

   protected void finalize() throws Throwable {
		this.local_flush(); //@ nowarn Modifies;
		super.finalize();
   } //@ nowarn; // Post;
	
	public static void printlnWithTrace(int level, String msg) {
		if (! DEBUG) 
			return;
		StackTraceElement te = getTraceElement(level + 4);
		Logger.println(msg + " ==> " + te); //$NON-NLS-1$
	}
	
	private static StackTraceElement getTraceElement(int level) {
//		StackTraceElement[] trace = Thread.currentThread().getStackTrace();
//		return (trace.length >= level && 0 <= level)
//			 ? trace[level]
//			 : null;
		return null;
	}
	
}
