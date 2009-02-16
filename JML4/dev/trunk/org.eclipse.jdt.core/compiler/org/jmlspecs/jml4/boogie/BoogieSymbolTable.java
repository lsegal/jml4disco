package org.jmlspecs.jml4.boogie;

import java.util.ArrayList;
import java.util.Hashtable;

public class BoogieSymbolTable {
	private final static String charmap = "abcdefghijklmnopqrstuvwxyz"; //$NON-NLS-1$
	private String generatedSymbol = ""; //$NON-NLS-1$
	private ArrayList scope = new ArrayList();
	private int scopeIndex = -1;
	
	public BoogieSymbolTable() {
		enterScope();
	}
	
	public void enterScope() {
		scopeIndex++;
		if (scopeIndex >= scope.size()) {
			scope.add(new Hashtable());
		}
	}
	
	public void exitScope(boolean ignoreRemoveScope) {
		if (!ignoreRemoveScope) {
			scope.remove(scopeIndex);
		}
		scopeIndex--;
	}
	
	public void exitScope() {
		exitScope(false);
	}
	
	public synchronized String addSymbol(String symbol) {
		Hashtable lastScope = (Hashtable)scope.get(scopeIndex);
		if (lastScope.get(symbol) != null) {
			throw new IllegalArgumentException("Symbol " + symbol + " already exists"); //$NON-NLS-1$ //$NON-NLS-2$
		}
		String value = generateSymbol();
		lastScope.put(symbol, value);
		return value;
	}
	
	public String lookup(String symbol) {
		// look through scopes (last to first)
		for (int i = scopeIndex; i >= 0; i--) {
			Hashtable tab = (Hashtable)scope.get(i);
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
