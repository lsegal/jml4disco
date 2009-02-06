package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.QualifiedTypeReference;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlQualifiedTypeReference extends QualifiedTypeReference implements JmlTypeReference {
	
	public Nullity nullity;
	private long ownershipModifiers;

	public JmlQualifiedTypeReference(char[][] sources, long[] poss, Nullity nullity, long ownershipModifiers) {
		super(sources, poss);
		this.setNullity(nullity);
		this.ownershipModifiers = ownershipModifiers;
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

	public void setNullity(Nullity nullity) {
		this.nullity = nullity;
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
