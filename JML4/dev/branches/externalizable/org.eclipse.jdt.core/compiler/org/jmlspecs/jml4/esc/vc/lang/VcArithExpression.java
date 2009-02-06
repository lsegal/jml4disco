package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcArithExpression extends VcBinaryExpression {

	// DISCO VcOperator no longer final to allow serialization
	public VcOperator operator;

	/*required for externalization*/
	public VcArithExpression() {}  

	public void readExternal(ObjectInput in) throws IOException,
	ClassNotFoundException {
		super.readExternal(in);
		this.operator = new VcOperator();
		this.operator.readExternal(in);
	}

	public void writeExternal(ObjectOutput out) throws IOException {
		super.writeExternal(out);
		this.operator.writeExternal(out);
	}
	
	public VcArithExpression(VcOperator operator, VC left, VC right, TypeBinding type,
			KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(left, right, type, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.operator = operator;
	}

	public VcArithExpression(VcOperator operator, VC left, VC right, TypeBinding type,
			int sourceStart, int sourceEnd) {
		super(left, right, type, sourceStart, sourceEnd);
		this.operator = operator;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public String toString() {
		return declString()+ "(" + this.left + " " + this.operator.name + " " + this.right + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

	/*package*/ VC inline(Map map) {
		VC lefts = this.left.inlineAndAddDecls(map);
		VC rights = this.right.inlineAndAddDecls(map);
		if (this.left.equals(lefts) && this.right.equals(rights))
			return this;
		return new VcArithExpression(this.operator, lefts, rights, this.type, this.sourceStart, this.sourceEnd);
	}
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + left.hashCode();
		result = prime * result + right.hashCode();
		result = prime * result + operator.hashCode();
		return result;
	}
}
