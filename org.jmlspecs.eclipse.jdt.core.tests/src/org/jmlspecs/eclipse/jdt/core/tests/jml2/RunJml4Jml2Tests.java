package org.jmlspecs.eclipse.jdt.core.tests.jml2;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class RunJml4Jml2Tests extends TestCase {

	public RunJml4Jml2Tests() {
	}

	public RunJml4Jml2Tests(String name) {
		super(name);
	}

	public static Test suite() {
		TestSuite suite = new TestSuite(RunJml4Jml2Tests.class.getName());
		suite.addTestSuite(JML2TestCase.class);
		return suite;
	}
}
