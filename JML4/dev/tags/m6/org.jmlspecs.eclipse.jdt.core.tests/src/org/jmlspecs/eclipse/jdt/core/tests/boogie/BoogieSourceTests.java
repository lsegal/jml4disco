package org.jmlspecs.eclipse.jdt.core.tests.boogie;

import junit.framework.TestCase;

import org.eclipse.jdt.internal.compiler.ast.TrueLiteral;
import org.jmlspecs.jml4.boogie.BoogieSource;
import org.jmlspecs.jml4.boogie.BoogieSourcePoint;

public class BoogieSourceTests extends TestCase {
	
	public void testPrepend() {
		BoogieSource b = new BoogieSource();
		
		assertTrue(b.getResults().equals(BoogieSource.getHeaders()));
		
		String prepend = "This will now be prepended";
		b.prepend(prepend);
		
		assertTrue(b.getResults().equals(BoogieSource.getHeaders() + prepend + "\n"));
		
		String toBeAppended = "true";
		b.append(toBeAppended, new TrueLiteral(0, 4));
		
		assertTrue(toBeAppended.equals(b.getTermAtPoint(new BoogieSourcePoint(5, 1)).toString()));
	}
	
	public void testEmpty() {
		BoogieSource b = new BoogieSource();
		String prepend = "";
		b.prepend(prepend);
		
		assertTrue(b.getResults().equals(BoogieSource.getHeaders()));
	}
	
	public void testTwoPrepends() {
		BoogieSource b = new BoogieSource();
		String prepend1 = "1";
		String prepend2 = "2";
		b.prepend(prepend1);
		
		assertTrue(b.getResults().equals(BoogieSource.getHeaders()+prepend1+"\n"));
		
		b.prepend(prepend2);
		
		assertTrue(b.getResults().equals(BoogieSource.getHeaders()+prepend2+"\n"+prepend1+"\n"));
	}
	
	public void testPrependNewline() {
		BoogieSource b = new BoogieSource();
		String prepend = "\n";
		
		b.prepend(prepend);
		
		assertTrue(b.getResults().equals(BoogieSource.getHeaders()+prepend));
	}
	
	public void testManyLineStatement() {
		BoogieSource b = new BoogieSource();
		String prepend = "This is a string that needs to be prepended\n" +
				"However it happens on multiple lines";
		
		b.prepend(prepend);
		
		assertTrue(b.getResults().equals(BoogieSource.getHeaders()+prepend+"\n"));
		
		prepend += "\n";
		b.prepend(prepend);
		
		assertTrue(b.getResults().equals(BoogieSource.getHeaders()+prepend+prepend));
	}
	

}
