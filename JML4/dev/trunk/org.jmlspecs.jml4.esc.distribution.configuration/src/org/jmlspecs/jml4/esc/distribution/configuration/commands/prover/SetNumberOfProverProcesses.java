package org.jmlspecs.jml4.esc.distribution.configuration.commands.prover;

import org.jmlspecs.jml4.esc.distribution.configuration.FrontCommand;
import org.jmlspecs.jml4.esc.distribution.configuration.CommandInput;
import org.jmlspecs.jml4.esc.distribution.configuration.exceptions.FrontControllerException;

public class SetNumberOfProverProcesses extends FrontCommand {

	@Override
	public void execute(CommandInput arg) throws FrontControllerException {
		String proverName = arg.getParameter("Prover-Name");
		if(proverName!=null) {
			FrontCommand addProverProcessesCommand;
			try {
				addProverProcessesCommand = (FrontCommand) Class.forName("org.jmlspecs.jml4.esc.distribution.configuration.commands.prover.setNumberOfProverProcesses.SetNumberOf"+proverName+"Processes").newInstance();
				addProverProcessesCommand.execute(arg);
			} catch (Exception e) {
				throw new FrontControllerException(e);
			}
		}
	}

	
	
}
