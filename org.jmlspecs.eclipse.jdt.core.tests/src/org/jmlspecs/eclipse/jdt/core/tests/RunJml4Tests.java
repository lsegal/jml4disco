package org.jmlspecs.eclipse.jdt.core.tests;

import org.jmlspecs.eclipse.jdt.core.tests.dbc.RunJml4DbcTests;
import org.jmlspecs.eclipse.jdt.core.tests.esc.RunJml4EscTests;
import org.jmlspecs.eclipse.jdt.core.tests.fspv.RunJml4FspvTests;
import org.jmlspecs.eclipse.jdt.core.tests.jml2.RunJml4Jml2Tests;
import org.jmlspecs.eclipse.jdt.core.tests.nonnull.RunJml4NonNullTests;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

/**
 * Runs all JML4 tests.
 */
public class RunJml4Tests extends TestCase {

	public RunJml4Tests(String name) {
		super(name);
	}
	public static Test suite() {
		TestSuite suite = new TestSuite(RunJml4Tests.class.getName());
		suite.addTest(RunJml4Jml2Tests.suite());
		suite.addTest(RunJml4NonNullTests.suite());
		suite.addTest(RunJml4DbcTests.suite());
		suite.addTest(RunJml4EscTests.suite());
		suite.addTest(RunJml4FspvTests.suite());
		return suite;
	}
}
