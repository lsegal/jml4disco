package org.jmlspecs.jml4.boogie.ast;

public abstract class Visitor {
	public boolean visit(AssertStatement term) { return true; }
	public boolean visit(AssumeStatement term) { return true; }
	public boolean visit(Assignment term) { return true; }
	public boolean visit(Axiom term) { return true; }
	public boolean visit(BinaryExpression term) { return true; }
	public boolean visit(BooleanLiteral term) { return true; }
	public boolean visit(BreakStatement term) { return true; }
	public boolean visit(CallStatement term) { return true; }
	public boolean visit(ConstStatement term) { return true; }
	public boolean visit(FunctionCall term) { return true; }
	public boolean visit(IfStatement term) { return true; }
	public boolean visit(IntLiteral term) { return true; }
	public boolean visit(LabelStatement term) { return true; }
	public boolean visit(MapTypeReference term) { return true; }
	public boolean visit(MapVariableReference term) { return true; }
	public boolean visit(Procedure term) { return true; }
	public boolean visit(Program term) { return true; }
	public boolean visit(ResultReference term) { return true; }
	public boolean visit(ReturnStatement term) { return true; }
	public boolean visit(TypeDeclaration term) { return true; }
	public boolean visit(TypeReference term) { return true; }
	public boolean visit(VariableDeclaration term) { return true; }
	public boolean visit(VariableReference term) { return true; }
	public boolean visit(VariableStatement term) { return true; }
	public boolean visit(WhileStatement term) { return true; }

	public void endVisit(AssertStatement term) { /* nothing */ }
	public void endVisit(AssumeStatement term) { /* nothing */ }
	public void endVisit(Assignment term) { /* nothing */ }
	public void endVisit(Axiom term) { /* nothing */ }
	public void endVisit(BinaryExpression term) { /* nothing */ }
	public void endVisit(BooleanLiteral term) { /* nothing */ }
	public void endVisit(BreakStatement term) { /* nothing */ }
	public void endVisit(CallStatement term) { /* nothing */ }
	public void endVisit(ConstStatement term) { /* nothing */ }
	public void endVisit(FunctionCall term) { /* nothing */ }
	public void endVisit(IfStatement term) { /* nothing */ }
	public void endVisit(IntLiteral term) { /* nothing */ }
	public void endVisit(LabelStatement term) { /* nothing */ }
	public void endVisit(MapTypeReference term) { /* nothing */ }
	public void endVisit(MapVariableReference term) { /* nothing */ }
	public void endVisit(Procedure term) { /* nothing */ }
	public void endVisit(Program term) { /* nothing */ }
	public void endVisit(ResultReference term) { /* nothing */ }
	public void endVisit(ReturnStatement term) { /* nothing */ }
	public void endVisit(TypeDeclaration term) { /* nothing */ }
	public void endVisit(TypeReference term) { /* nothing */ }
	public void endVisit(VariableDeclaration term) { /* nothing */ }
	public void endVisit(VariableReference term) { /* nothing */ }
	public void endVisit(VariableStatement term) { /* nothing */ }
	public void endVisit(WhileStatement term) { /* nothing */ }
}
