package org.jmlspecs.jml4.esc.distribution.configuration.commands.prover.setNumberOfProverProcesses;

import org.jmlspecs.jml4.esc.distribution.configuration.FrontCommand;
import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;
import org.jmlspecs.jml4.esc.provercoordinator.prover.isabelle.IsabelleProcessPool;

public class SetNumberOfIsabelleProcesses extends FrontCommand {

	@Override
	public void execute(CommandInput arg) throws FrontControllerException {
		try {
			String max_process_string =  arg.getParameter("MaxProcess");
			if(max_process_string!=null) {
				int max_process = Integer.parseInt(max_process_string);
				IsabelleProcessPool.getInstance().setMAX_PROCESS(max_process);
				arg.setAttribute("out", "The number of Isabelle processes has been set to "+max_process);
			}
		}
		catch(Exception e) {
			throw new FrontControllerException(e);
		}
	}
	
}
