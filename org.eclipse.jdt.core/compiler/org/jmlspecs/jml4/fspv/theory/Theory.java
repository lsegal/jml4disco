/**
 * 
 */
package org.jmlspecs.jml4.fspv.theory;

import org.jmlspecs.jml4.fspv.Fspv;

/**
 * @author karabot
 *
 */
public class Theory {

	public final String name;
	public final TheoryLemma [] lemmas;
	
	public Theory(String name, TheoryLemma[] lemmas) {
		this.name = name;
		this.lemmas = lemmas;
	}
	
	public String toString() {
		String s = this.name;
		s+= "\n" + Fspv.pretyPrintArray(this.lemmas); //$NON-NLS-1$
		return s;
	}
	
	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}
	
}
