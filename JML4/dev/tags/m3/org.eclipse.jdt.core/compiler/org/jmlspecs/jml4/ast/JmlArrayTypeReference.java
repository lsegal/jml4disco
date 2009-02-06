package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ArrayTypeReference;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlArrayTypeReference extends ArrayTypeReference implements JmlTypeReference {
	private Nullity nullity;
	private long ownershipModifiers;
	public final /*@nullable*/ Nullity[] elemNullities;

	public JmlArrayTypeReference(char[] source, int dimensions, long pos, Nullity[] elemNullities, Nullity nullity, long ownershipModifiers) {
		super(source, dimensions, pos);
		this.setNullity(nullity);
		this.ownershipModifiers = ownershipModifiers;
		this.elemNullities = elemNullities;
	}

	public void setNullity(Nullity nullity) {
		this.nullity = nullity;
	}

	public Nullity getNullity() {
		return this.nullity;
	}

	public boolean isDeclaredNonNull() {
		return this.nullity.isNon_null();
	}
	public boolean isDeclaredMonoNonNull() {
		return this.nullity.isMono_non_null();
	}

	public StringBuffer printExpression(int indent, StringBuffer output){
		if (JmlAstUtils.useSupersToStringMethod)
			return super.printExpression(indent, output);
		return super.printExpression(indent, output.append(" /*@ "+this.nullity.toString()+" */ ")); //$NON-NLS-1$//$NON-NLS-2$
	}
	
	public String fullyQualifiedToString(){
		String n = " /*@ "+this.nullity.toString()+" */ "; //$NON-NLS-1$//$NON-NLS-2$
		String t = super.toString();
		return n + t;
	}
	public boolean isPeer() {
		return JmlModifier.isPeer(this.ownershipModifiers);
	}
	public boolean isReadonly() {
		return JmlModifier.isReadonly(this.ownershipModifiers);
	}
	public boolean isRep() {
		return JmlModifier.isRep(this.ownershipModifiers);
	}
}
