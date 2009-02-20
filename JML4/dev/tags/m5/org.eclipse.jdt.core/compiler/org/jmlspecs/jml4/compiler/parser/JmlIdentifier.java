package org.jmlspecs.jml4.compiler.parser;

/**
 * This is a helper class for the Parser. Instances of this class are meant to
 * hold JML keyword identifiers ...
 */
public class JmlIdentifier {
	private char[] token;
	private int id; // value of TokenNamexxx for this token
	private boolean hasRedundantSuffix;
	private long pos;

	private/*@nullable*/String tokenAsString = null;
	private int start = -1;
	private int end = -1;

	public JmlIdentifier(char[] token, boolean hasRedundantSuffix, int id, long pos) {
		this.token = token;
		this.hasRedundantSuffix = hasRedundantSuffix;
		this.pos = pos;
		this.id = id;
	}

	public int sourceStart() {
		if (this.start == -1) {
			this.start = (int) (pos >>> 32);
		}
		return this.start;
	}

	public int sourceEnd() {
		if (this.end == -1) {
			this.end = (int) pos;
		}
		return this.end;
	}

	public char[] token() {
		return token;
	}

	public void setToken(char[] token) {
		this.token = token;
	}

	public int id() {
		return id;
	}

	public void setId(int id) {
		this.id = id;
	}

	public long getPos() {
		return pos;
	}

	public void setPos(long pos) {
		this.pos = pos;
	}

	public boolean hasRedundantSuffix() {
		return hasRedundantSuffix;
	}

	public void setHasRedundantSuffix(boolean hasRedundantSuffix) {
		this.hasRedundantSuffix = hasRedundantSuffix;
	}

	public String toString() {
		if (this.tokenAsString == null) {
			this.tokenAsString = new String(this.token);
		}
		return this.tokenAsString;
	}
}
