package org.jmlspecs.eclipse.jdt.core.tests.boogie;

import junit.framework.Test;
import junit.framework.TestSuite;

public class AllTests {

	public static Test suite() {
		TestSuite suite = new TestSuite(
				"Test for org.jmlspecs.eclipse.jdt.core.tests.boogie");
		//$JUnit-BEGIN$
		suite.addTestSuite(BoogieSourceTests.class);
		suite.addTestSuite(BoogieSymbolTableTests.class);
		suite.addTestSuite(TranslationTests.class);
		suite.addTestSuite(AdapterTests.class); // adapters go last
		//$JUnit-END$
		return suite;
	}

}
