package org.jmlspecs.eclipse.jdt.core.tests.esc.casestudy;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class RunJml4EscCaseStudyTests extends TestCase {

	public RunJml4EscCaseStudyTests() {
	}

	public RunJml4EscCaseStudyTests(String name) {
		super(name);
	}

	public static Test suite() {
		TestSuite suite = new TestSuite(RunJml4EscCaseStudyTests.class.getName());
		suite.addTestSuite(QueensTests.class);
		suite.addTestSuite(FindTests.class);
		suite.addTestSuite(EuclidTests.class);
		suite.addTestSuite(FactorialTests.class);
//		suite.addTestSuite(QuicksortTests.class);
//		suite.addTestSuite(BagTests.class);
		return suite;
	}
}
