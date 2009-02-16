package org.jmlspecs.eclipse.jdt.core.tests.boogie;

import org.jmlspecs.jml4.boogie.BoogieSymbolTable;

import junit.framework.TestCase;

public class BoogieSymbolTableTests extends TestCase {
	public void testSymbolAddition() {
		BoogieSymbolTable tab = new BoogieSymbolTable();
		assertEquals("a", tab.addSymbol("x"));
		assertEquals("a", tab.lookup("x"));
	}

	public void testDuplicateSymbolAdditionShouldFail() {
		BoogieSymbolTable tab = new BoogieSymbolTable();
		tab.addSymbol("x");
		assertEquals("a", tab.lookup("x"));
		try {
			tab.addSymbol("x");
			fail("Duplicate symbol addition should fail.");
		}
		catch (IllegalArgumentException e) {
			assertEquals("Symbol x already exists", e.getMessage());
		}
	}
	
	public void testEnterScope() {
		BoogieSymbolTable tab = new BoogieSymbolTable();
		tab.addSymbol("x");
		assertEquals("a", tab.lookup("x"));
		tab.enterScope();
		tab.addSymbol("x");
		assertEquals("b", tab.lookup("x"));
	}
	
	public void testExitScope() {
		BoogieSymbolTable tab = new BoogieSymbolTable();
		tab.addSymbol("x");
		assertEquals("a", tab.lookup("x"));
		tab.enterScope();
		tab.addSymbol("x");
		assertEquals("b", tab.lookup("x"));
		tab.exitScope();
		assertEquals("a", tab.lookup("x"));
	}
	
	public void testMissingSymbol() {
		BoogieSymbolTable tab = new BoogieSymbolTable();
		
		assertEquals(null, tab.lookup("x"));

		tab.enterScope();
		tab.addSymbol("x");
		tab.exitScope();
		assertEquals(null, tab.lookup("x"));
	}
	
	public void testSymbolInHigherScope() {
		BoogieSymbolTable tab = new BoogieSymbolTable();
		tab.enterScope();
		tab.addSymbol("x");
		tab.enterScope();
		tab.enterScope();
		assertEquals("a", tab.lookup("x"));
	}

	public void testSymbolGenerator() {
		BoogieSymbolTable tab = new BoogieSymbolTable();
		
		for (int i = 0; i < 26; i++) tab.addSymbol("x" + i);
		assertEquals("aa", tab.addSymbol("test"));
		assertEquals("aa", tab.lookup("test"));
		
		for (int i = 0; i < 25; i++) tab.addSymbol("y" + i);
		tab.addSymbol("test2");
		assertEquals("ba", tab.lookup("test2"));
		assertEquals("ba", tab.lookup("test2"));
	}
}
