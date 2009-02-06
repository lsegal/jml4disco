package org.jmlspecs.eclipse.jdt.core.tests.esc;

import org.jmlspecs.jml4.esc.PostProcessor;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class RunJml4EscTests extends TestCase {

	public RunJml4EscTests() {
	}

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		PostProcessor.useOldErrorReporting = true;
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		PostProcessor.useOldErrorReporting = false;
	}

	public RunJml4EscTests(String name) {
		super(name);
	}

	public static Test suite() {
		TestSuite suite = new TestSuite(RunJml4EscTests.class.getName());
		suite.addTestSuite(ArrayTests.class);
		suite.addTestSuite(FieldTests.class);
		suite.addTestSuite(InitialTests.class);
		suite.addTestSuite(QuantifierTests.class);
		suite.addTestSuite(ReportedBugsTests.class);
		suite.addTestSuite(SanityTests.class);
		suite.addTestSuite(SimplifyTests.class);
		suite.addTestSuite(WhileTests.class);
		return suite;
	}
}
