package org.jmlspecs.eclipse.jdt.core.tests;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import org.jmlspecs.eclipse.jdt.core.tests.dbc.RunJml4DbcTests;
import org.jmlspecs.eclipse.jdt.core.tests.jml2.RunJml4Jml2Tests;
import org.jmlspecs.eclipse.jdt.core.tests.nonnull.RunJml4NonNullTests;

/**
 * Runs all JML4 tests except for those for Esc4 & Fspv.
 */
public class RunJml4_WithoutEsc4_Tests extends TestCase {

	public RunJml4_WithoutEsc4_Tests(String name) {
		super(name);
	}
	public static Test suite() {
		TestSuite suite = new TestSuite(RunJml4_WithoutEsc4_Tests.class.getName());
		suite.addTest(RunJml4Jml2Tests.suite());
		suite.addTest(RunJml4NonNullTests.suite());
		suite.addTest(RunJml4DbcTests.suite());
		return suite;
	}
}
