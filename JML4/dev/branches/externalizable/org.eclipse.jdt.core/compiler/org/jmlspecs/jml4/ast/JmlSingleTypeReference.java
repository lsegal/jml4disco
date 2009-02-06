package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.SingleTypeReference;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlSingleTypeReference extends SingleTypeReference implements JmlTypeReference {

	private Nullity nullity;
	private long ownershipModifiers;
	
	public JmlSingleTypeReference(char[] source, long pos, Nullity nullity, long ownershipModifiers) {
		super(source, pos);
		this.setNullity(nullity);
		this.ownershipModifiers = ownershipModifiers;
	}

	public JmlSingleTypeReference(SingleTypeReference type, Nullity nullity, long ownershipModifiers) {
		super(type.toString().toCharArray(), type.sourceStart);
		this.setNullity(nullity);
		this.ownershipModifiers = ownershipModifiers;
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
		return super.printExpression(indent,
				JmlAstUtils.useSupersToStringMethod
				? output
				: output.append("/*@"+this.nullity+"*/ ")); //$NON-NLS-1$ //$NON-NLS-2$
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
