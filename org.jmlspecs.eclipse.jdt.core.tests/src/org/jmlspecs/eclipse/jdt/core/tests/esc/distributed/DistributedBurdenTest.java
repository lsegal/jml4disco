package org.jmlspecs.eclipse.jdt.core.tests.esc.distributed;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestResult;
import junit.framework.TestSuite;

/**
 * In order to run this test, you must first comment out the method call to
 * assertUniqueScenario(String) in createPerformanceMeter(String)
 * org.eclipse.test.performance:org.eclipse.test.internal.performance.PerformanceMeterFactory
 * @author group0j
 *
 */
public class DistributedBurdenTest extends TestCase {


	private final int NB_OF_LOOPS = 3;

	public DistributedBurdenTest(String name) {
		super(name);
	}

	/**
	 * This will loop through the Test suite and 
	 * respond with either a successful or unsuccessful message
	 */
	public void testBurden()
	{
		//Test largeTest;
		for(int i = 0; i < NB_OF_LOOPS; i ++)
		{
			System.out.println("Starting Next Test: #" + i);
			Test largeTest = makeSuite();
			TestResult result = new TestResult();
			largeTest.run(result);
			if(result.wasSuccessful())
				System.out.println("#"+ i + " was Successful");
			else
				System.out.println("#"+ i + " was Unsuccessful");
		}
	}


	/**
	 * Collects other tests into a suite and returns it
	 * @return A suite composed of multiple tests
	 */
	public Test makeSuite()
	{
		TestSuite suite = new TestSuite("Suite");
		//suite.addTestSuite(BigEscTests.class);
		suite.addTestSuite(BigEscTests.class);
		suite.addTestSuite(DistributedWhileTests.class);
		suite.addTestSuite(BigWhileTests.class);
		//suite.addTestSuite(SanityTests.class);
		//suite.addTestSuite(DistributedWhileTests.class);
		return suite;		
	}

}
