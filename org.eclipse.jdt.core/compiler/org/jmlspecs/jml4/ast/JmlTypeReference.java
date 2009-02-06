package org.jmlspecs.jml4.ast;

import org.jmlspecs.jml4.nonnull.Nullity;

public interface JmlTypeReference {
	void setNullity(Nullity nullity);
    Nullity getNullity();
    
    // subclasses must override this method!
    // the one from TypeRefence is NOT good enough, since it always returns true;
    boolean isDeclaredNonNull();
    boolean isDeclaredMonoNonNull();
    
	boolean isPeer();
	boolean isReadonly();
	boolean isRep();
}