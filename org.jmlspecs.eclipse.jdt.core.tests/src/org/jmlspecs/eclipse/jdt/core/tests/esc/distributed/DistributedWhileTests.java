package org.jmlspecs.eclipse.jdt.core.tests.esc.distributed;

import java.util.Map;

import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.jmlspecs.eclipse.jdt.core.tests.esc.WhileTests;
import org.jmlspecs.jml4.compiler.JmlCompilerOptions;
import org.jmlspecs.jml4.esc.provercoordinator.strategy.ProveVcDistributed;

public class DistributedWhileTests extends WhileTests {

	public DistributedWhileTests(String name) {
		super(name);
	}
	
	@Override
	@SuppressWarnings("unchecked")
	protected Map<String, String> getCompilerOptions() {
		Map<String, String> options = super.getCompilerOptions();
		options.put(JmlCompilerOptions.OPTION_EscDistributedPropertiesFile, "proverCoordinatorUrls.properties");
		options.put(JmlCompilerOptions.OPTION_EscDistributedEnabled,  CompilerOptions.ENABLED);
		options.put(JmlCompilerOptions.OPTION_EscProverStrategy, ProveVcDistributed.getName());
		return options;
	}

}
