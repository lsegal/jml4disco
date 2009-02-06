package org.jmlspecs.eclipse.jdt.core.tests.fspv;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class RunJml4FspvTests  extends TestCase {

	public RunJml4FspvTests() {
	}

	public RunJml4FspvTests(String name) {
		super(name);
	}
	
	public static Test suite() {
		TestSuite suite = new TestSuite(RunJml4FspvTests.class.getName());
		suite.addTestSuite(WhileTests.class);
		return suite;
	}
}
