package org.jmlspecs.jml4.esc.vc.lang;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.esc.gc.lang.KindOfAssertion;

public abstract class VcBinaryExpression extends VC {
	public final VC left;
	public final VC right;

	public VcBinaryExpression(VC left, VC right, TypeBinding type, KindOfAssertion kindOfAssertion, int kindOfLabel, int sourceStart, int sourceEnd, int labelStart) {
		super(type, kindOfAssertion, kindOfLabel, sourceStart, sourceEnd, labelStart);
		this.left = left;
		this.right = right;
	}

	public VcBinaryExpression(VC left, VC right, TypeBinding type, int sourceStart, int sourceEnd) {
		super(type, sourceStart, sourceEnd);
		this.left = left;
		this.right = right;
	}

	public List/*<VcVarDecl>*/ getVarDecls() {
		List/*<VcVarDecl>*/ result= new ArrayList/*<VcVarDecl>*/();
		result.addAll(this.decls());
		result.addAll(this.left.decls());
		result.addAll(this.right.decls());
		return result;
	}
}
