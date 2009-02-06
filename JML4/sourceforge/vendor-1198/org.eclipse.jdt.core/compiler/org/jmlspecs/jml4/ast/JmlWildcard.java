package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.Wildcard;
import org.jmlspecs.jml4.nonnull.Nullity;

public class JmlWildcard extends Wildcard implements JmlTypeReference {

	private Nullity nullity;
	private long ownershipModifiers;

	public JmlWildcard(int kind, Nullity nullity, long ownershipModifiers) {
		super(kind);
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
