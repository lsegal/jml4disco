package org.jmlspecs.eclipse.jdt.ui;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;


import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;

import org.eclipse.core.runtime.ILog;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.jmlspecs.eclipse.jdt.internal.compiler.util.Log;

public class Console extends Log {
    /** Creates a Console Log and sets the current log object
     * 
     * @param consoleName The name of the console to be logged to
     * @param plugin The plugin object using this log
     */
    //@ requires consoleName != null;
    //@ modifies log;
    //@ ensures log != null && \fresh(log);
    //@ ensures log.consoleName == consoleName;
    public static void createLog(String consoleName, Plugin plugin) {
        Console c = new Console(consoleName,plugin);
        log = c;
        System.setOut(c.consolePrintStream());
        System.setErr(c.consolePrintStream());
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
        return ((Console)log).consolePrintStream();
    }

    //==============================================================

    /** Creates a new Log utility object
     * 
     * @param consoleName The name of the console to be logged to
     * @param plugin The plugin object using this log
     */
    //@ requires consoleName != null;
    //@ requires plugin != null;
    //@ modifies \nothing;
    //@ ensures \result.consoleName == consoleName;
    private Console(String consoleName, Plugin plugin) {
        this.consoleName = consoleName;
        this.pluginLog = plugin.getLog();
        this.pluginID = plugin.getBundle().getSymbolicName();
    }

    // This model variable models the content of the material
    // sent to the log.
    //@ model public String content;

    /** The name of the console that this plugin writes to. */
    //@ constraint \not_modified(consoleName);
    //@ invariant consoleName != null;
    //@ spec_public
    private String consoleName;

    /** The ILog of the plugin that this Log object connects to */
    //@ constraint \not_modified(pluginLog);
    //@ invariant pluginLog != null;
    //@ spec_public
    private ILog pluginLog;

    /** The id of the plugin using this log */
    //@ constraint \not_modified(plugiID);
    //@ invariant pluginID != null;
    //@ spec_public
    private String pluginID;

    // TODO: Perhaps provide
    // a way to introduce other logging mechanisms.  One could
    // argue that the various options allowed here should just
    // be instances of different logging mechanisms.  That is a
    // degree of freedom we don't need right at the moment, though
    // it does make for a nice modular design.

    /** Cached value of the MessageConsole object */
    private MessageConsole console = null;
    //@ private constraint \old(console) != null ==> \not_modified(console);

    /** Cached value of the stream to use to write to the console */
    private MessageConsoleStream stream = null;
    //@ private constraint \old(stream) != null ==> \not_modified(stream);

    /** Creates, if necessary, and returns an instance of
     *  the stream to use to write to the console
     * @return The stream value to use
     */
    //@ ensures \result != null;
    public MessageConsoleStream getConsoleStream() {
        IConsoleManager consoleManager = ConsolePlugin.getDefault().getConsoleManager();
        IConsole[] existing = consoleManager.getConsoles();
        for (int i=0; i<existing.length; ++i) {
            if (existing[i].getName().equals(consoleName)) {
                console = (MessageConsole)existing[i];
                break;
            }
        }
        if (console == null) {
            console = new MessageConsole(consoleName,null);
            consoleManager.addConsoles(new IConsole[]{console});
        }
        stream = console.newMessageStream();
        return stream;
    }

    /** Color to use for error messages */
    // FIXME - should get this color from the system preferences
    static final private Color errorColor = new Color(null,255,0,0);

    /**
     * Records an informational message 
     * @param msg The message to log
     */
    //@ requires msg != null;
    //@ modifies content;
    public void ilog(String msg) {
        getConsoleStream().println(msg);
        // Also write it to the log file, if requested.
//      if (alsoLogInfo) {
//      pluginLog.log(
//      new Status(Status.INFO, 
//      pluginID,
//      Status.OK, msg, null));
//      }
    }


    /**
     * Records an error message
     * @param msg The message to log
     * @param e An associated exception (may be null)
     */
    //@ requires msg != null;
    //@ modifies content;
    public void ierrorlog(String msg, Throwable e) {
        // Always put errors in the log
        pluginLog.log(
                new Status(Status.ERROR, 
                        pluginID,
                        Status.OK, msg, e));
        MessageConsoleStream cs = getConsoleStream();
        Color c = cs.getColor();
        cs.setColor(errorColor);
        cs.println(msg);
        cs.setColor(c);
    }

    /**
     * Creates a PrintStream that, when written to, writes to the Eclipse Console
     * of the current log object
     * 
     * @return a PrintStream connected to the Eclipse Console
     */
    public PrintStream consolePrintStream() {
        return new PrintStream(new StreamToConsole(getConsoleStream()));
    }

    /**
     * This class is an OutputStream that, when written to, writes
     * the data to the Eclipse Console supplied 
     * in the constructor.  
     * This requires converting from
     * the byte data written to the Stream into character data that is
     * written to a MessageConsole; thus a specific Charset is required.
     * 
     * @author David R. Cok
     */
    public static class StreamToConsole extends OutputStream {
        protected ByteBuffer bb = ByteBuffer.allocate(2000);
        protected char[] input = new char[1];
        protected CharBuffer output = CharBuffer.allocate(2000);
        protected char[] outputchar = new char[2000];
        protected int len;
        protected CharsetDecoder decoder;

        /** The output console, set by the constructor. */
        //@ constraint \not_modified(console);
        //@ invariant console != null;
        protected MessageConsoleStream console;

        /**
         * Constructs an OutputStream that is connected to the 
         * given console.
         * @param console The console to write to via the OutputStream
         */
        public StreamToConsole(MessageConsoleStream console) {
            // FIXME - should use default charset for System.out
            // or set the charset from an argument
            decoder = Charset.forName("UTF-8").newDecoder();
            this.console = console;
        }

        // This implementation does not use the charset, because I
        // can't get the decoder to work in the code below.  FIXME
        public void write(int b) {
            outputchar[0] = (char)b;
            len = 1;
            dump(false);
        }

        public void write(byte[] b,int off, int len) {
            while (len > 0) {
                int n = len;
                if (n > outputchar.length) n = outputchar.length;
                for (int k=0; k<n; ++k) outputchar[k] = (char)b[off+k];
                this.len = n;
                dump(false);
                off += n;
                len -= n;
            }
        }

        /**
         * This writes everything from the outputchar buffer to the 
         * Console
         * @param end true if the stream should be flushed
         */
        private void dump(boolean end) {
            if (len == 0) return;
            console.print(new String(outputchar,0,len));
            len = 0;
        }

//      public void write(int b) throws IOException {
//      bb.put((byte)b);
//      dump(false);
//      }

//      public void write(byte[] b,int off, int len) throws IOException {
//      bb.put(b,off,len);
//      dump(false);
//      }

//      private void dump(boolean end) {
//      CoderResult cr;
//      do {
//      cr = decoder.decode(bb,output,end);
//      System.out.println("CR " + cr.toString());
//      int len;
//      while ((len = 7) > 0) {
//      if (len > outputchar.length) len = outputchar.length;
//      output.get(outputchar,0,len);
//      System.out.println("OUT " + new String(outputchar,0,len));
//      //getConsoleStream().print(new String(outputchar,0,len));
//      }
//      output.compact();
//      } while (false && cr.isOverflow());
//      bb.compact();
//      }

        public void flush() throws IOException {
            dump(true);
            //decoder.flush(output);
        }

        public void close() {
            bb = null;
            output = null;
            decoder = null;
        }
    }
}
