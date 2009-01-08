package org.jmlspecs.jml4.fspv.theory;

public class TheoryQuantifier {

	public static final String EXISTS = "\\<exists>"; //$NON-NLS-1$
	public static final String FORALL = "\\<forall>"; //$NON-NLS-1$
	public static final String MAX = "max"; //$NON-NLS-1$
	public static final String MIN = "min"; //$NON-NLS-1$
	public static final String NUM_OF = "\\<Sum>"; //$NON-NLS-1$
	public static final String SUM = "\\<Sum>"; //$NON-NLS-1$
	public static final String PRODUCT = "\\<Prod>"; //$NON-NLS-1$

	private String qop;
	
	private TheoryQuantifier(String qop) {
		this.qop = qop;
	}

	public boolean isExists() {
		return this.qop.equals(EXISTS);
	}
	
	public boolean isForall() {
		return this.qop.equals(FORALL);
	}

	public boolean isMax() {
		return this.qop.equals(MAX);
	}

	public boolean isMin() {
		return this.qop.equals(MIN);
	}

	public boolean isSum() {
		return this.qop.equals(SUM);
	}

	public boolean isProduct() {
		return this.qop.equals(PRODUCT);
	}

	public String toString() {
		return this.qop;
	}
	
	public static TheoryQuantifier exists() {
		return new TheoryQuantifier(EXISTS);
	}

	public static TheoryQuantifier forall() {
		return new TheoryQuantifier(FORALL);
	}

	public static TheoryQuantifier max() {
		return new TheoryQuantifier(MAX);
	}

	public static TheoryQuantifier min() {
		return new TheoryQuantifier(MIN);
	}

	public static TheoryQuantifier numOf() {
		return new TheoryQuantifier(NUM_OF);
	}

	public static TheoryQuantifier sum() {
		return new TheoryQuantifier(SUM);
	}

	public static TheoryQuantifier product() {
		return new TheoryQuantifier(PRODUCT);
	}

}
