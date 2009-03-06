package org.jmlspecs.jml4.boogie;

import java.util.Hashtable;

import org.eclipse.jdt.internal.compiler.ast.Block;
import org.eclipse.jdt.internal.compiler.ast.MethodDeclaration;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;

/**
 * Maintains and passifies local variable symbols in a {@link MethodDeclaration}.
 * Passification means that each local variable will have a block-independent, unique
 * symbol representing the variable name.
 */
public class BoogieSymbolTable {
	private class BoogieSymbol {
		public String symbol;
		public TypeReference type;
		
		public BoogieSymbol(String symbol, TypeReference type) {
			this.symbol = symbol;
			this.type = type;
		}
	}
	
	private final static String charmap = "abcdefghijklmnopqrstuvwxyz"; //$NON-NLS-1$
	private String generatedSymbol = ""; //$NON-NLS-1$
	private Hashtable scope = new Hashtable();
	private Hashtable heirarchy = new Hashtable();
	private Block currentBlock = null;
	
	public BoogieSymbolTable() {
		enterScope(new Block(0));
	}
	
	/**
	 * The current block representing the variable scope.
	 * 
	 * @return the current block
	 */
	public Block getCurrentBlock() {
		return currentBlock;
	}
	
	/**
	 * Enters a new block (which is used to represent variable scope), updating the current block.
	 * 
	 * @param block the block to enter
	 */
	public void enterScope(Block block) {
		if (currentBlock != null) { 
			heirarchy.put(block, currentBlock);
		}
		
		currentBlock = block;
		if (scope.get(currentBlock) == null) {
			scope.put(block, new Hashtable());
		}
	}
	
	/**
	 * Exits the current scope (block) by setting current block to
	 * its parent block.
	 */
	public void exitScope() {
		currentBlock = (Block)heirarchy.get(currentBlock);
	}
	
	/**
	 * Adds a symbol to the current block
	 * @param symbol the symbol to add
	 * @return the generated passified representation of the symbol (same value
	 * 		as subsequent calls to {@link #lookup(String)})
	 */
	public synchronized String addSymbol(String symbol) {
		return addSymbol(symbol, null);
	}

	/**
	 * Adds a symbol to the current block
	 * @param symbol the symbol to add
	 * @param type the type reference associated with the symbol
	 * @return the generated passified representation of the symbol (same value
	 * 		as subsequent calls to {@link #lookup(String)})
	 */
	public synchronized String addSymbol(String symbol, TypeReference type) {
		Hashtable lastScope = (Hashtable)scope.get(currentBlock);
		if (lastScope.get(symbol) != null) {
			throw new IllegalArgumentException("Symbol " + symbol + " already exists"); //$NON-NLS-1$ //$NON-NLS-2$
		}
		String value = generateSymbol();
		lastScope.put(symbol, new BoogieSymbol(value, type));
		return value;
	}
	
	/**
	 * Looks for a symbol name associated with the last entered block 
	 * (via {@link #enterScope(Block)}), {@link #getCurrentBlock()}.  
	 * @param symbol the symbol name to look for
	 * @return the unique block-independent symbol representation for the
	 * 		   symbol name.
	 * @see #lookup(String, Block)
	 */
	public String lookup(String symbol) {
		return lookup(symbol, currentBlock);
	}

	/**
	 * Looks for a symbol name associated with a specific block scope and
	 * returns the unique symbol value representing it.
	 * 
	 * @param symbol the symbol name
	 * @param block the block object maintaining symbol scopes 
	 * @return the passified unique symbol value
	 */
	public String lookup(String symbol, Block block) {
		BoogieSymbol bSym = lookupSymbol(symbol, block);
		return bSym != null ? bSym.symbol : null;
	}
	
	/**
	 * Looks for a symbol name associated with the last entered block 
	 * (via {@link #enterScope(Block)}), {@link #getCurrentBlock()}.  
	 * @param symbol the symbol name to look for
	 * @return the type represented by the symbol
	 * @see #lookup(String, Block)
	 */
	public TypeReference lookupType(String symbol) {
		return lookupType(symbol, currentBlock);
	}
	
	/**
	 * Looks for a symbol name associated with the last entered block 
	 * (via {@link #enterScope(Block)}), {@link #getCurrentBlock()}.  
	 * @param symbol the symbol name to look for
	 * @return the type represented by the symbol
	 */
	public TypeReference lookupType(String symbol, Block block) {
		BoogieSymbol bSym = lookupSymbol(symbol, block);
		return bSym != null ? bSym.type : null;
	}
	
	/**
	 * Gets the BoogieSymbol associated with a specific block scope and
	 * returns the unique symbol value representing it.
	 * 
	 * @param symbol the symbol name
	 * @param block the block object maintaining symbol scopes 
	 * @return the BoogieSymbol object holding symbol and type information
	 */
	private BoogieSymbol lookupSymbol(String symbol, Block block) {
		// look through scopes (last to first)
		while (block != null) {
			Hashtable tab = (Hashtable)scope.get(block);
			BoogieSymbol val = (BoogieSymbol)tab.get(symbol);
			if (val != null) return val;
			block = (Block)heirarchy.get(block);
		} 
		return null;
	}
	
	/**
	 * Generates a new unique symbol name, also storing it as {@link #generatedSymbol}.
	 *  
	 * @return the next symbol value (the value of {@link #generatedSymbol})
	 */
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
