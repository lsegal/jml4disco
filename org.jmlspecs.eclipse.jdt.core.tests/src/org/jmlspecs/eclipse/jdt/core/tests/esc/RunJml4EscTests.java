package org.jmlspecs.eclipse.jdt.core.tests.esc;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class RunJml4EscTests extends TestCase {

	public RunJml4EscTests() {
	}

	public RunJml4EscTests(String name) {
		super(name);
	}

	public static Test suite() {
		TestSuite suite = new TestSuite(RunJml4EscTests.class.getName());
		suite.addTestSuite(SanityTests.class);
		suite.addTestSuite(SimplifyTests.class);
		suite.addTestSuite(InitialTests.class);
		suite.addTestSuite(QuantifierTests.class);
		suite.addTestSuite(WhileTests.class);
//		suite.addTestSuite(ArrayTests.class);
//		suite.addTestSuite(FieldTests.class);
		suite.addTestSuite(ReportedBugsTests.class);
		return suite;
	}
}
