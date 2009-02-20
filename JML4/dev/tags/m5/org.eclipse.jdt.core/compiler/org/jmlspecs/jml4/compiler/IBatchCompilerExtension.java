package org.jmlspecs.jml4.compiler;

import java.util.Map;

//@ non_null_by_default
public interface IBatchCompilerExtension {

	public final int ARG_NOT_HANDLED = -1;
	
    /** This processes command-line arguments for extensions to the compiler.
     * @param currentArg The command-line argument currently under consideration
     * @param args The whole list of arguments
     * @param index The location of currentArg in the list
     * @return ARG_NOT_HANDLED if nothing has been recognized,
     *    otherwise i >= index and is the last argument position processed
     *    (not one beyond it).
     */
    //@ requires 0 <= index && index < args.length;
    //@ requires currentArg.equals(args[index]);
    //@ ensures \result == ARG_NOT_HANDLED
    //@      || index <= \result && \result < args.length;
    public int configureArgs(
    		String currentArg,
    		String[] args, 
    		int index, 
    		Map options);

    public boolean handleWarningToken(String token, boolean isEnabling, Map optionsMap);
}
