package org.jmlspecs.jml4.boogie.ast;

public class ResultReference extends VariableReference {
	public ResultReference(Procedure scope) {
		super(TOKEN_RESULT, scope.getJavaNode(), scope);
	}

	public void traverse(Visitor visitor) {
		visitor.visit(this);
		visitor.endVisit(this);
	}
}
