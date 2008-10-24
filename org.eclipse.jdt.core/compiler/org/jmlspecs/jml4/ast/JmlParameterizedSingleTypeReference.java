package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ParameterizedSingleTypeReference;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlParameterizedSingleTypeReference extends
		ParameterizedSingleTypeReference
		implements JmlTypeReference {

	private Nullity nullity;
	private final long ownershipModifiers;
	private final Nullity[] elemNullities;
	
	public JmlParameterizedSingleTypeReference(char[] name,
			TypeReference[] typeArguments, int dim, long pos, 
			Nullity nullity, 
			Nullity[] elemNullities, 
			long ownershipModifiers) {
		super(name, typeArguments, dim, pos);
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


	public TypeReference copyDims(int dim, Nullity[] elemNullities, Nullity nullity, long ownershipModifiers) {
		return new JmlParameterizedSingleTypeReference(this.token, this.typeArguments, dim, (((long)this.sourceStart)<<32)+this.sourceEnd, nullity, elemNullities, ownershipModifiers);
	}

	public StringBuffer printExpression(int indent, StringBuffer output){
		if (JmlAstUtils.useSupersToStringMethod)
			return super.printExpression(indent, output);
		return super.printExpression(indent, output.append("/*@ "+this.nullity.toString()+" */ ")); //$NON-NLS-1$ //$NON-NLS-2$
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
