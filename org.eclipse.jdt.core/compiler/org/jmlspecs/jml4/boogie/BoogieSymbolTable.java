package org.jmlspecs.jml4.boogie;

import java.util.Hashtable;

import org.eclipse.jdt.internal.compiler.ast.Block;

public class BoogieSymbolTable {
	private final static String charmap = "abcdefghijklmnopqrstuvwxyz"; //$NON-NLS-1$
	private String generatedSymbol = ""; //$NON-NLS-1$
	private Hashtable scope = new Hashtable();
	private Hashtable heirarchy = new Hashtable();
	private Block currentBlock = null;
	
	public BoogieSymbolTable() {
		enterScope(new Block(0));
	}
	
	public void enterScope(Block block) {
		if (currentBlock != null) { 
			heirarchy.put(block, currentBlock);
		}
		
		currentBlock = block;
		if (scope.get(currentBlock) == null) {
			scope.put(block, new Hashtable());
		}
	}
	
	public void exitScope() {
		currentBlock = (Block)heirarchy.get(currentBlock);
	}
	
	public synchronized String addSymbol(String symbol) {
		Hashtable lastScope = (Hashtable)scope.get(currentBlock);
		if (lastScope.get(symbol) != null) {
			throw new IllegalArgumentException("Symbol " + symbol + " already exists"); //$NON-NLS-1$ //$NON-NLS-2$
		}
		String value = generateSymbol();
		lastScope.put(symbol, value);
		return value;
	}
	
	public String lookup(String symbol) {
		// look through scopes (last to first)
		for (Block block = currentBlock; block != null; 
				block = (Block)heirarchy.get(block)) {
			Hashtable tab = (Hashtable)scope.get(block);
			String val = (String)tab.get(symbol);
			if (val != null) return val;
		} 
		return null;
	}
	
	private synchronized String generateSymbol() {
		if (generatedSymbol == "") { //$NON-NLS-1$
			generatedSymbol = new String(new char[]{charmap.charAt(0)}, 0, 1);
			return generatedSymbol;
		}
		
		char[] sym = generatedSymbol.toCharArray();
		for (int symindex = sym.length - 1; symindex >= 0; symindex--) {
			char c = sym[symindex];
			int index = charmap.indexOf(c);
			if (index + 1 >= charmap.length()) {
				c = charmap.charAt(0);
				if (symindex == 0) {
					// increment the string length ("zzz" turns into "aaaa")
					sym = new char[sym.length + 1];
					for (int i = 0; i < sym.length; i++) {
						sym[i] = c;
					}
					break;
				}
				
				// make everything else "a" ("azzz" goes to "baaa")
				for (int i = symindex; i < sym.length; i++) { 
					sym[i] = c;
				}
			}
			else {
				sym[symindex] = charmap.charAt(index + 1);
				break;
			}
		}
		
		generatedSymbol = new String(sym);
		return generatedSymbol;
	}
}
