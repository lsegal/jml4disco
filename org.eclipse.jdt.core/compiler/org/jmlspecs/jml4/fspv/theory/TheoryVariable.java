package org.jmlspecs.jml4.fspv.theory;

public class TheoryVariable {
	public static final int ARGUMENT = 0;
	public static final int RESULT = 1;
	public static final int OLD = 2;
	public static final int LOCAL = 3;
	public static final int BOUND = 4;
	public static final String OLD_SUFFIX = "_old"; //$NON-NLS-1$
	public static final String RESULT_NAME = "result'"; //$NON-NLS-1$

	public final String name;
	public final TheoryType type;
	public final int kind;
	public final TheoryExpression initialization;
	public final int declSourceStart;

	public TheoryVariable(String name, TheoryType type2, TheoryExpression initialization, int kind, int declSourceStart) {
		this.name=name;
		this.type=type2;
		this.kind=kind;
		this.initialization = initialization;
		this.declSourceStart = declSourceStart;
	}

	public String getDecoratedName() {
		String retVal = this.name;
		if(this.isOld())
			retVal += OLD_SUFFIX;
		return retVal;
	}
	
	public TheoryType getType() {
		return this.type;
	}
	
	public int getDeclSourceStart() {
		return this.declSourceStart;
	}
	
	public boolean isArgument() {
		return this.kind == ARGUMENT;
	}

	public boolean isResult() {
		return this.kind == RESULT;
	}
	
	public boolean isOld() {
		return this.kind == OLD;
	}

	public boolean isLocal() {
		return this.kind == LOCAL;
	}

	public boolean isBound() {
		return this.kind == BOUND;
	}

	
	public TheoryVariableReference nameReference() {
		return new TheoryVariableReference(this);
	}

	public String toString() {
		return this.getDecoratedName() + TheoryType.TYPE_SEPARATOR + this.type;
	}

	public Object visit(TheoryVisitor visitor) {
		return visitor.accept(this);
	}

	public static TheoryVariable Argument(String name, TheoryType type, int declSourceStart) {
		return new TheoryVariable(name, type, null, ARGUMENT, declSourceStart);
	}

	public static TheoryVariable Result(TheoryType type) {
		return new TheoryVariable(RESULT_NAME, type, null, RESULT, 0);
	}
	
	public static TheoryVariable Old(TheoryVariable v) {
		if(v.isOld())	return v;
		return new TheoryVariable(v.name, v.type, v.initialization, OLD, v.declSourceStart);
	}

	public static TheoryVariable Local(String name, TheoryType type, TheoryExpression initialization, int declSourceStart) {
		return new TheoryVariable(name, type, initialization, LOCAL, declSourceStart);
	}

	public static TheoryVariable Bound(String name, TheoryType type,	TheoryExpression initialization, int declSourceStart) {
		return new TheoryVariable(name, type, initialization, BOUND, declSourceStart);
	}

	public boolean equals(TheoryVariable v) {
		return this.name.equals(v.name) && this.declSourceStart == v.declSourceStart;
	}

}
