package org.jmlspecs.jml4.boogie;

/**
 * Represents a point in a Boogie source code file. Used
 * to map points in Boogie source back to a Java source file.
 */
public class BoogieSourcePoint {
	public int row; 
	public int col;

	/**
	 * Holds a point in Boogie source code.
	 * 
	 * @param row the row for the Boogie code position
	 * @param col the column for the Boogie code position
	 */
	public BoogieSourcePoint(int row, int col) { 
		this.row = row; 
		this.col = col;
	}
	
	/**
	 * Creates a copy of the source point object 
	 * pointing to the same row and column.
	 */
	/* @Override */
	public Object clone() {
		return new BoogieSourcePoint(row, col);
	}

	/**
	 * Compares this point to another BoogieSourcePoint by
	 * verifying that the rows and columns are equal.
	 */
	public boolean equals(Object other) {
		BoogieSourcePoint lp = (BoogieSourcePoint)other;
		return row == lp.row && col == lp.col;
	}	
	
	public int hashCode() {
		return new Integer(row + col).hashCode();
	}

}
