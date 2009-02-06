package org.jmlspecs.jml4.esc.vc.lang;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.util.Map;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;
import org.jmlspecs.jml4.esc.provercoordinator.prover.ProverVisitor;

public class VcRelativeExpression extends VcBinaryExpression {

	//DISCO removed private to allow serialization
	public VcOperator operator;
	
	public VcRelativeExpression() {}  
	
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

	public VcRelativeExpression(VcOperator operator, VC left, VC right, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(left, right, TypeBinding.BOOLEAN, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.operator = operator;
	}

	public VcRelativeExpression(VcOperator operator, VC left, VC right, int sourceStart, int sourceEnd) {
		super(left, right, TypeBinding.BOOLEAN, sourceStart, sourceEnd);
		this.operator = operator;
	}

	public String accept(ProverVisitor visitor) {
		return visitor.visit(this);
	}

	public String acceptAsTerm(ProverVisitor visitor) {
		return visitor.visitAsTerm(this);
	}

	public String toString() {
		return declString()+ "(" + this.left + " " + this.operator.name + " " + this.right + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$ //$NON-NLS-4$
	}

	/*package*/ VC inline(Map map) {
		VC lefts = this.left.inlineAndAddDecls(map);
		VC rights = this.right.inlineAndAddDecls(map);
		if (this.left.equals(lefts) && this.right.equals(rights))
			return this;
		return new VcRelativeExpression(this.operator, lefts, rights, this.sourceStart, this.sourceEnd);
	}
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
		result = prime * result + ((operator == null) ? 0 : operator.hashCode());
		return result;
	}
}
