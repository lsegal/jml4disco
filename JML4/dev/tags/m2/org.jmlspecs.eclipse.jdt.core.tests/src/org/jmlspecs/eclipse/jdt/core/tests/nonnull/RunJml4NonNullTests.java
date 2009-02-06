package org.jmlspecs.eclipse.jdt.core.tests.nonnull;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class RunJml4NonNullTests extends TestCase {

	public RunJml4NonNullTests() {
	}

	public RunJml4NonNullTests(String name) {
		super(name);
	}

	public static Test suite() {
		TestSuite suite = new TestSuite(RunJml4NonNullTests.class.getName());
		suite.addTestSuite(Jml5StyleNullity.class);
		suite.addTestSuite(NNTS_ArrayTestCompiler.class);
		suite.addTestSuite(NNTS_MonoTestCompiler.class);
		suite.addTestSuite(NNTS_MonoTestRuntime.class);
		suite.addTestSuite(NullTypeSystemTestCompiler.class);
		suite.addTestSuite(NullTypeSystemTestJml2.class);
		suite.addTestSuite(NullTypeSystemTestRuntime.class);
		suite.addTestSuite(SanityTests.class);
		return suite;
	}
}
