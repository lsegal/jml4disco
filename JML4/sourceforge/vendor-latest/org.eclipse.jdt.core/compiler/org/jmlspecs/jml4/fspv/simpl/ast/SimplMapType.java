package org.jmlspecs.jml4.fspv.simpl.ast;

public class SimplMapType extends SimplType {

	public final SimplType domain;
	public final SimplType range;

	public SimplMapType(SimplType domain, SimplType type) {
		this.domain = domain;
		this.range = type;
	}

}
