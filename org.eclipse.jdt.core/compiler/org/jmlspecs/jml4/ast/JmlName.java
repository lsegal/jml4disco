package org.jmlspecs.jml4.ast;

import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Expression;

// Really FIXME: rename this to JmlNameOrSuffix
public class JmlName extends ASTNode {

    public static final int SORT_MIN      = 1;
    public static final int SORT_IDENT    = 1;
    public static final int SORT_THIS     = 2; 
    public static final int SORT_SUPER    = 3;
	public static final int SORT_WILDCARD = 4; // *
    public static final int SORT_POS      = 5; // [ exp ]
    public static final int SORT_RANGE    = 6; // [lo .. hi]
    public static final int SORT_ALL      = 7; // [*]
    public static final int SORT_MAX      = SORT_ALL;

	public final String name;

	public final int sort;
	//@ invariant SORT_MIN <= this.sort && this.sort <= SORT_MAX;

	private final /*@ nullable */ Expression index1;
	//@ invariant (sort == SORT_POS || sort == SORT_RANGE) == (index1 != null);

	private final /*@ nullable */ Expression index2;
	//@ invariant (sort == SORT_RANGE) == (index2 != null);

	public final long position;
	
	//@ ensures this.name == name;
	//@ ensures this.index1 == null & this.index2 == null;
	/*@ ensures (SORT_IDENT <= this.sort && this.sort <= SORT_WILD) 
	  @      || this.sort == SORT_ALL;
      @*/
	public JmlName(String name, int sourceStart, int sourceEnd) {
		this.name = name;
		this.sort = name2sort(name);
		this.index1 = this.index2 = null;
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
		this.position = (((long) sourceStart) << 32) + sourceEnd;  
	}

	//@ ensures this.index1 == pos & this.index2 == null;
	//@ ensures SORT_POS == this.sort; 
	public JmlName(Expression pos, int sourceStart, int sourceEnd) {
		this.index1 = pos;
		this.sort = SORT_POS;
		this.name = "[" + pos.toString() + "]";  //$NON-NLS-1$//$NON-NLS-2$
		this.index2 = null;
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
		this.position = (((long) sourceStart) << 32) + sourceEnd; 
	}

	//@ ensures this.index1 == low & this.index2 == hi;
	//@ ensures SORT_RANGE == this.sort; 
	public JmlName(Expression low, Expression hi, int sourceStart, int sourceEnd) {
		this.index1 = low;
		this.index2 = hi;
		this.sort = SORT_RANGE;
		this.name = "[" + low.toString() + ".." + hi.toString() + "]"; //$NON-NLS-1$//$NON-NLS-2$//$NON-NLS-3$
		this.sourceStart = sourceStart;
		this.sourceEnd = sourceEnd;
		this.position = (((long) sourceStart) << 32) + (sourceEnd - 1); 
	}

	//@ ensures SORT_MIN <= \result && \result <= SORT_MAX;
	private static /*@ pure */ int name2sort(String name) {
		if (name.equals("this"))  return SORT_THIS; //$NON-NLS-1$
		if (name.equals("super")) return SORT_SUPER; //$NON-NLS-1$
		if (name.equals("*"))     return SORT_WILDCARD; //$NON-NLS-1$
		if (name.equals("[*]"))   return SORT_ALL; //$NON-NLS-1$
		return SORT_IDENT;
	}

	//@ ensures \result == (SORT_POS == this.sort || this.sort == SORT_RANGE || this.sort == SORT_ALL);
	public boolean isArraySuffix() {
		return SORT_POS <= this.sort && this.sort <= SORT_ALL;
	}

	public StringBuffer print(int indent, StringBuffer output) {
		return output.append(this.name);
	}
	
	public Expression getPositionExp() {
		if (this.sort != JmlName.SORT_POS) {
			// report a problem.
			throw new RuntimeException();
		}
		
		return this.index1;
	}
	
	public Expression getLowRange() {
		if (this.sort != JmlName.SORT_RANGE) {
			// report a problem.
			throw new RuntimeException();
		}
		
		return this.index1;
	}
	
	public Expression getHighRange() {
		if (this.sort != JmlName.SORT_RANGE) {
			// report a problem.
			throw new RuntimeException();
		}
		
		return this.index2;
	}

}
