package org.jmlspecs.jml4.esc.result.lang;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverAdapter;
// DISCO Serializable
public class Result implements Serializable{

	public static final Result[] EMPTY = new Result[0];
	public static final Result[] VALID = new Result[] {new Result()};

	private final boolean isValid;
	private final boolean isAssertionFailure;
	private final /*@nullable*/KindOfAssertion kindOfAssertion;
	private final int assertionPosition;
	private final int failedExprStart;
	private final int failedExprEnd;
	private /*@nullable*/String vcName;
	
	public Result() {
		this.isValid = true;
		this.isAssertionFailure = false;
		this.kindOfAssertion = null;
		this.assertionPosition = -1;
		this.failedExprStart = -1;
		this.failedExprEnd = -1;
	}
	
	public Result(KindOfAssertion kindOfAssertion, int assertionPosition, int failedExprStart, int failedExprEnd) {
		this.isValid = false;
		this.isAssertionFailure = true;
		this.kindOfAssertion = kindOfAssertion;
		this.assertionPosition = assertionPosition;
		this.failedExprStart = failedExprStart;
		this.failedExprEnd = failedExprEnd;
	}

	public String toString() {
		String s = this.isValid
		         ? ProverAdapter.VALID
		         : this.kindOfAssertion + "("+this.assertionPosition+") at ("+this.failedExprStart+", "+this.failedExprEnd+")";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
		return "[Result: " + s + "]";  //$NON-NLS-1$//$NON-NLS-2$
	}

	public static boolean isValid(/*@nullable*/Result[] results) {
		boolean result = results != null && results.length == 1 && results[0].isValid;
		return result;
	}

	public static Result[] removeDuplicates(Result[] results) {
		List/*<Result>*/ result = new ArrayList/*<Result>*/();
		boolean duplicateFound = false;
		for (int i = 0; i < results.length; i++) {
			Result result_i = results[i];
			if (result.contains(result_i)) {
				duplicateFound = true;
			} else {
				result.add(result_i);
			}
		}
		return duplicateFound
			 ? (Result[])result.toArray(EMPTY)
		     : results;
	}

	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + this.toString().hashCode();
		return result;
	}

	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Result other = (Result) obj;
		if (isValid != other.isValid)
			return false;
		else if (isAssertionFailure != other.isAssertionFailure)
			return false;
		else if (kindOfAssertion != other.kindOfAssertion)
			return false;
		else if (assertionPosition != other.assertionPosition)
			return false;
		else if (failedExprStart != other.failedExprStart)
			return false;
		else if (failedExprEnd != other.failedExprEnd)
			return false;
		return true;
	}

	public boolean isValid() {
		return this.isValid;
	}

	public KindOfAssertion kindOfAssertion() {
		return this.kindOfAssertion;
	}

	public int failedExprStart() {
		return this.failedExprStart;
	}

	public int failedExprEnd() {
		return this.failedExprEnd;
	}

	public int assertionPosition() {
		return this.assertionPosition;
	}

	public void setVcName(/*@nullable*/ String name) {
		this.vcName = name;
	}
	
	public /*@nullable*/String vcName() {
		return this.vcName;
	}
}
