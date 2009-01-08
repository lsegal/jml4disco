package org.jmlspecs.eclipse.jdt.core.tests.dbc;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class RunJml4DbcTests extends TestCase {

	public RunJml4DbcTests() {
	}

	public RunJml4DbcTests(String name) {
		super(name);
	}

	public static Test suite() {
		TestSuite suite = new TestSuite(RunJml4DbcTests.class.getName());
		suite.addTestSuite(AnnotatedLoopTest.class);
		suite.addTestSuite(AssignableTestCompiler.class);
		suite.addTestSuite(ConstraintsTest.class);
		suite.addTestSuite(DataGroupTestCompiler.class);
		suite.addTestSuite(DbcTestCompiler.class);
		suite.addTestSuite(DbcTestRuntime_2.class);
		suite.addTestSuite(DbcTestRuntime.class);
		suite.addTestSuite(ImpliesTestRuntime.class);
		suite.addTestSuite(OldTest.class);
		suite.addTestSuite(QuantifierTest.class);
		suite.addTestSuite(SetComprehensionTest.class);
		suite.addTestSuite(SetStatementTest.class);
		suite.addTestSuite(SignalsTestCompiler.class);
		suite.addTestSuite(SubtypeExpressionTest.class);
		suite.addTestSuite(TypeTest.class);
		return suite;
	}
}
