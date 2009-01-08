package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ArrayQualifiedTypeReference;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlArrayQualifiedTypeReference extends ArrayQualifiedTypeReference implements JmlTypeReference {

	public /*@ non_null */ Nullity nullity;
	private long ownershipModifiers;
	public final Nullity[] elemNullities;

	public JmlArrayQualifiedTypeReference(char[][] sources, int dim, long[] poss, Nullity[] elemNullities, /*@ non_null */ Nullity nullity, long ownershipModifiers) {
		super(sources, dim, poss);
		this.nullity = nullity;
		this.ownershipModifiers = ownershipModifiers;
		this.elemNullities = elemNullities;
	}

    public boolean isDeclaredNonNull() {
    	return this.nullity.isNon_null();
    }
    public boolean isDeclaredMonoNonNull() {
    	return this.nullity.isMono_non_null();
    }

	public void setNullity(/*@ non_null */ Nullity nullity) {
		this.nullity = nullity;
	}
    public /*@ non_null */ Nullity getNullity() {
    	return this.nullity;
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
